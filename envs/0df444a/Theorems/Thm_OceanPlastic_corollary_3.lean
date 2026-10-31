-- Prove2me | Theorems.Thm_OceanPlastic_corollary_3
-- name    : OceanPlastic.corollary_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:35.197978+00:00
-- url     : https://prove2.me/theorems/b17bde58-466c-4d94-b812-aadad1c3723f
-- title:
--   Corollary 3 — the for-profit optimum without additionality
-- statement:
--   Let the firm be a profit maximizer ($\rho_1=1$, $\rho_2=\rho_3=0$), with $\delta_o^2kQ_o\le2M\bar v_o$. The unique optimal solution of the no-additionality variant of (4) is
--   $$\hat d_o=\min\Bigl\{\frac{Q_o}{2},\ \max\Bigl\{\frac{Mp_m}{2k},\ \frac{MQ_o[(1-\delta_o)p_m+\bar v_o]}{2M\bar v_o+4k(1-\delta_o)Q_o}\Bigr\}\Bigr\},$$
--   $$\hat r=\Bigl[\frac{\bar v_o(kQ_o-\tfrac12Mp_m)}{M\bar v_o+2kQ_o(1-\delta_o)}-\frac12p_m\Bigr]^+.$$
--
--   With $\hat p_m=\dfrac{kQ_o\bar v_o}{(1-\delta_o)kQ_o+M\bar v_o}$, every optimal solution satisfies:
--
--   1. $\hat r>0$ if and only if $p_m<\hat p_m$;
--   2. $S^O(\hat r)>0$ if and only if $p_m<\hat p_m$;
--   3. if $c_E^r>0$, then $E^O(\hat r)>0$ if and only if $p_m<\hat p_m$.
--
--   This is the second optimum compared in Proposition 5: without additionality a firm facing a high local price induces no extra recycling at all.
--
--   Differences from the source:
--   - reading: "Ê^O > 0, Ŝ^O > 0 if and only if p_m < p̂_m" → r̂ > 0 ↔ p_m < p̂_m and Ŝ^O > 0 ↔ p_m < p̂_m unconditionally; Ê^O > 0 ↔ p_m < p̂_m under c_E^r > 0; reason: E^O(r) = c_E^r M r/(2k) vanishes at c_E^r = 0, and the paper gives c_E^r no sign
--   - reading: "the equilibrium outcomes" → (r, d) optimal for the variant ↔ (r, d) is the printed pair; reason: the equilibrium is the optimal solution of the firm's problem, which the paper treats as unique
--   - reading: v̄_o(kQ_o − 1/2Mp_m) → v̄_o(kQ_o − (1/2)·M·p_m); reason: the proof's case (i), p. 47, and Proposition 10's proof use this parse
--   - encoding: Assumption 1(2) at ρ_1 = 1, ρ_2 = ρ_3 = 0: δ_o ≤ √(2Mv̄_o/(kQ_o)) → δ_o² k Q_o ≤ 2 M v̄_o; reason: equivalent since δ_o ≥ 0; (1) is 1 > 0 and (3) concerns Case S only
--   - reading: M, v̄_o, Q_o unspecified positive sizes; p_m a price; c_E^r with no stated sign → real M, v̄_o, Q_o > 0, p_m ≥ 0, c_E^r ≥ 0 (fields of Params), with k > 0, δ_o ∈ [0,1), ρ_p ∈ (0,1] as printed; reason: sizes, a price and a value; v̄_o is the upper end of a uniform law; M is real as in the paper, which differentiates in M
-- source:
--   Baron–Romero–Zhang–Zhou, Innovative Business Models in Ocean-Bound Plastic Recycling, MSOM, doi:10.1287/msom.2022.0643, Corollary 3, p.35

import Mathlib
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark
import Definitions.Def_OceanPlastic_CaseO
import Definitions.Def_OceanPlastic_Problem4

namespace OceanPlastic

open Params

/-- **Corollary 3: the for-profit optimum without additionality.** Baron–Romero–Zhang–Zhou, MSOM,
doi:10.1287/msom.2022.0643, Corollary 3, p. 35.

Take the for-profit weights `ρ₁ = 1`, `ρ₂ = ρ₃ = 0` and `δ_o² k Q_o ≤ 2 M v̄_o`. The unique optimal
solution of the no-additionality variant of (4) is
`d̂_o = min {Q_o / 2, max {M p_m / (2k), M Q_o [(1 − δ_o) p_m + v̄_o] / (2 M v̄_o + 4 k (1 − δ_o) Q_o)}}`,
`r̂ = [v̄_o (k Q_o − M p_m / 2) / (M v̄_o + 2 k Q_o (1 − δ_o)) − p_m / 2]⁺`.
Moreover every optimal solution has `r > 0 ↔ p_m < p̂_m`, `S^O(r) > 0 ↔ p_m < p̂_m` and, if
`c_E^r > 0`, `E^O(r) > 0 ↔ p_m < p̂_m`, where `p̂_m = k Q_o v̄_o / ((1 − δ_o) k Q_o + M v̄_o)`.

**Formalization Note** The paper's "`Ê^O > 0`, `Ŝ^O > 0` iff `p_m < p̂_m`" needs `c_E^r > 0` for the
`Ê^O` part, because `E^O(r) = c_E^r M r / (2k)`. The denominators are positive for every
`P : Params`. -/
theorem corollary_3 (P : Params) (hA : P.δ ^ 2 * P.k * P.Q ≤ 2 * P.M * P.vbar) :
    (∀ r d : ℝ, P.IsOptimalNoAdd 1 0 0 r d ↔
      d = min (P.Q / 2) (max (P.M * P.pm / (2 * P.k))
        (P.M * P.Q * ((1 - P.δ) * P.pm + P.vbar) /
          (2 * P.M * P.vbar + 4 * P.k * (1 - P.δ) * P.Q))) ∧
      r = max (P.vbar * (P.k * P.Q - 1 / 2 * P.M * P.pm) /
          (P.M * P.vbar + 2 * P.k * P.Q * (1 - P.δ)) - 1 / 2 * P.pm) 0) ∧
    (∀ r d : ℝ, P.IsOptimalNoAdd 1 0 0 r d →
      (0 < r ↔ P.pm < P.pHat) ∧
      (0 < P.SO r ↔ P.pm < P.pHat) ∧
      (0 < P.cE → (0 < P.EO r ↔ P.pm < P.pHat))) := by sorry

end OceanPlastic
