-- Prove2me | Theorems.Thm_OceanPlastic_proposition_5
-- name    : OceanPlastic.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:28.92999+00:00
-- url     : https://prove2.me/theorems/fc9c7f0b-8e1f-4a44-8d75-8e55f5bb037f
-- title:
--   Proposition 5 (corrected: "only if" for $0<p_m<\hat p_m$) — additionality raises a for-profit firm's impacts when the offset market is small, lowers them when large
-- statement:
--   Let the firm be a profit maximizer ($\rho_1=1$, $\rho_2=\rho_3=0$), with $\delta_o^2kQ_o\le2M\bar v_o$ (Assumption 1(2) at these weights). Problem (4) has an optimal solution, and so does its no-additionality variant. Let $(\tilde r,\tilde d_o)$ be any optimal solution of (4), $(\hat r,\hat d_o)$ any optimal solution of the variant, and write $\tilde S=S^O(\tilde r)$, $\tilde E=E^O(\tilde r)$, $\hat S=S^O(\hat r)$, $\hat E=E^O(\hat r)$. Let
--   $$\bar Q_o=\frac{M\bar v_o}{k\delta_o},\qquad \hat p_m=\frac{kQ_o\bar v_o}{(1-\delta_o)kQ_o+M\bar v_o}.$$
--
--   1. If $Q_o\le\bar Q_o$, then $\tilde S\ge\hat S$ and $\tilde E\ge\hat E$.
--   2. If $Q_o>\bar Q_o$ and $0<p_m<\hat p_m$, then $\tilde S<\hat S$ and $\tilde E\le\hat E$, and $\tilde E<\hat E$ when $c_E^r>0$.
--   3. If $0<p_m\le\bar v_o$, then
--   $$\tilde S\ge\hat S\ \text{ and }\ \tilde E\ge\hat E\quad\text{if and only if}\quad Q_o\le\bar Q_o.$$
--
--   This is the paper's central finding on additionality: requiring the firm to sell offsets only on additionally recycled plastic does not always increase its social and environmental impacts. When the offset market is large relative to $\bar Q_o$, it lowers them.
--
--   **Formalization Note** $Q_o\le\bar Q_o$ is written $k\delta_oQ_o\le M\bar v_o$, and $p_m<\hat p_m$ with its positive denominator multiplied out.
--
--   Differences from the source:
--   - correction: S̃ ≥ Ŝ, Ẽ ≥ Ê if and only if Q_o ≤ Q̄_o, for all parameters → "if" for all p_m ≥ 0; "only if" (with strict "smaller") for 0 < p_m < p̂_m; the iff for 0 < p_m ≤ v̄_o; reason: at M = k = v̄_o = 1, δ_o = 1/2, Q_o = 3, ρ_p = c_E^r = 1 (so Q̄_o = 2 < Q_o) both p_m = 3/2 ≥ p̂_m (r̃ = r̂ = 0) and p_m = 0 (r̃ = r̂ = 3/4) give S̃ = Ŝ and Ẽ = Ê
--   - generalization: "(smaller)" when Q_o is large, with the closed form of Corollary 1(a) stated for p_m ≤ v̄_o → clause (ii) for all 0 < p_m < p̂_m, with strict S̃ < Ŝ (and Ẽ < Ê under c_E^r > 0); reason: for Q_o > Q̄_o one has p̂_m > v̄_o, so the range contains 0 < p_m ≤ v̄_o; it specializes to the printed "(smaller)"
--   - encoding: Q_o ≤ Q̄_o = Mv̄_o/(kδ_o) → k δ_o Q_o ≤ M v̄_o; reason: the same for δ_o > 0; at δ_o = 0 it is always true, matching the paper's remark (p. 19) that additionality then always gives larger impacts
--   - reading: "the equilibrium outcomes" ˜ and ˆ → every optimal solution of (4) at ρ = (1,0,0) and of its no-additionality variant, with existence of both asserted; reason: the equilibrium is the optimal solution of the firm's problem, which the paper treats as unique; existence prevents vacuity
--   - encoding: Assumption 1(2) at ρ_1 = 1, ρ_2 = ρ_3 = 0: δ_o ≤ √(2Mv̄_o/(kQ_o)) → δ_o² k Q_o ≤ 2 M v̄_o; reason: equivalent since δ_o ≥ 0; (1) is 1 > 0 and (3) concerns Case S only
--   - reading: M, v̄_o, Q_o unspecified positive sizes; p_m a price; c_E^r with no stated sign → real M, v̄_o, Q_o > 0, p_m ≥ 0, c_E^r ≥ 0 (fields of Params), with k > 0, δ_o ∈ [0,1), ρ_p ∈ (0,1] as printed; reason: sizes, a price and a value; v̄_o is the upper end of a uniform law; M is real as in the paper, which differentiates in M
--   - reading: collectors' total income → gross payment (price received) × (volume); reason: the only reading consistent with Π^B_C = Mp_m²/(4k), eq. (3) and Π^{OS}_C = kq_t²/M (p. 14); net utility would be half of it
-- source:
--   Baron–Romero–Zhang–Zhou, Innovative Business Models in Ocean-Bound Plastic Recycling, MSOM, doi:10.1287/msom.2022.0643, Proposition 5, p.18; proof, p.42; Corollary 1(a), p.18; Corollary 3, p.35

import Mathlib
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark
import Definitions.Def_OceanPlastic_CaseO
import Definitions.Def_OceanPlastic_Problem4

namespace OceanPlastic

open Params

/-- **Proposition 5 (corrected: "only if" needs `0 < p_m < p̂_m`): additionality raises a for-profit
firm's social and environmental impacts when the offset market is small, and lowers them when it is
large.** Baron–Romero–Zhang–Zhou, *Innovative Business Models in Ocean-Bound Plastic Recycling*, MSOM,
doi:10.1287/msom.2022.0643, Proposition 5, p. 18.

Take the for-profit weights `ρ₁ = 1`, `ρ₂ = ρ₃ = 0` and Assumption 1(2) at these weights,
`δ_o² k Q_o ≤ 2 M v̄_o`. Problem (4) and its no-additionality variant have optimal solutions, and for
every optimal `(r̃, d̃)` of (4) and every optimal `(r̂, d̂)` of the variant:
* (i) if `Q_o ≤ Q̄_o`, then `S̃ ≥ Ŝ` and `Ẽ ≥ Ê`, for every `p_m ≥ 0`;
* (ii) if `Q_o > Q̄_o` and `0 < p_m < p̂_m`, then `S̃ < Ŝ` and `Ẽ ≤ Ê`, and `Ẽ < Ê` if `c_E^r > 0`;
* (iii) if `0 < p_m ≤ v̄_o`, then `S̃ ≥ Ŝ ∧ Ẽ ≥ Ê` iff `Q_o ≤ Q̄_o`.

Here `Q̄_o = M v̄_o / (k δ_o)` and `p̂_m = k Q_o v̄_o / ((1 − δ_o) k Q_o + M v̄_o)`.

**Formalization Note** `Q_o ≤ Q̄_o` is written `k δ_o Q_o ≤ M v̄_o`, which also makes sense at
`δ_o = 0`, where the paper (p. 19) says additionality always gives larger impacts. `p_m < p̂_m` is
written with the positive denominator multiplied out. The printed "if and only if" for all parameters
is false: at `M = k = v̄_o = 1`, `δ_o = 1/2`, `Q_o = 3`, both `p_m = 3/2` and `p_m = 0` give
`r̃ = r̂` although `Q_o > Q̄_o = 2`. -/
theorem proposition_5 (P : Params) (hA : P.δ ^ 2 * P.k * P.Q ≤ 2 * P.M * P.vbar) :
    (∃ r d : ℝ, P.IsOptimal 1 0 0 r d) ∧
    (∃ r d : ℝ, P.IsOptimalNoAdd 1 0 0 r d) ∧
    ∀ rt dt rh dh : ℝ, P.IsOptimal 1 0 0 rt dt → P.IsOptimalNoAdd 1 0 0 rh dh →
      (P.k * P.δ * P.Q ≤ P.M * P.vbar → P.SO rt ≥ P.SO rh ∧ P.EO rt ≥ P.EO rh) ∧
      (P.M * P.vbar < P.k * P.δ * P.Q → 0 < P.pm →
        P.pm * ((1 - P.δ) * P.k * P.Q + P.M * P.vbar) < P.k * P.Q * P.vbar →
        P.SO rt < P.SO rh ∧ P.EO rt ≤ P.EO rh ∧ (0 < P.cE → P.EO rt < P.EO rh)) ∧
      (0 < P.pm → P.pm ≤ P.vbar →
        ((P.SO rt ≥ P.SO rh ∧ P.EO rt ≥ P.EO rh) ↔ P.k * P.δ * P.Q ≤ P.M * P.vbar)) := by sorry

end OceanPlastic
