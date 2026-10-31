-- Prove2me | Theorems.Thm_OceanPlastic_proposition_2a
-- name    : OceanPlastic.proposition_2a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:27.111226+00:00
-- url     : https://prove2.me/theorems/43222808-ed32-4a45-aa89-c81f7f0c3bde
-- title:
--   Proposition 2(a) — problem (4) reduces to a concave univariate problem
-- statement:
--   Let $\rho_2,\rho_3\ge0$ with $\rho_1>\max\{\rho_2,\rho_3\}$ and
--   $$\delta_o\le\sqrt{\frac{M\bar v_o\,(2\rho_1-(1+\rho_p)\rho_2)}{\rho_1kQ_o}}$$
--   (Assumption 1(1)–(2)). Write $\varphi(r)=T^O(d^O_o(r),r)$, where
--   $$d^O_o(r)=\min\Bigl\{\frac{Q_o(\bar v_o+\delta_o r)}{2\bar v_o},\,Q_o,\,\frac{Mr}{2k}\Bigr\}.$$
--
--   1. For every $r\ge0$, $(r,d^O_o(r))$ is feasible for (4), and $d^O_o(r)$ is the unique maximizer of $d\mapsto T^O(d,r)$ among the $d$ with $(r,d)$ feasible.
--   2. $(r,d)$ is an optimal solution of (4) if and only if $r\ge0$, $d=d^O_o(r)$ and $r$ maximizes $\varphi$ over $[0,\infty)$.
--   3. $\varphi$ is concave on $[0,\infty)$.
--   4. Problem (4) has an optimal solution.
--
--   This solves the firm's triple-bottom-line problem up to one concave maximization in the bonus.
--
--   Differences from the source:
--   - reading: "r^O is the equilibrium bonus, which can be obtained by solving … r^O = arg max_{r≥0} T^O(d^O_o(r), r)" → (r, d) optimal for (4) ↔ r ≥ 0, d = d^O_o(r) and r maximizes φ on [0,∞); existence asserted; no uniqueness claim; reason: at equality in Assumption 1(2), φ can be affine on the interior-d_o piece; the proof (pp. 35–36) optimizes sequentially, which is the inner-maximizer clause
--   - reading: "univariate convex optimization problem" → φ is concave on [0,∞); reason: a maximization of a concave function is the convex problem meant
--   - reading: weights "non-negative" and, in the next sentence, "positive constants" (p. 11) → ρ_2, ρ_3 ≥ 0 with ρ_1 > max{ρ_2, ρ_3}; reason: §5 uses ρ_2 = ρ_3 = 0, so non-negative is the reading the paper needs
--   - reading: Assumption 1 (1), (2), (3) → (1) and (2) only; reason: (3) involves the Case S parameters v̄_s, c_s, which do not occur in Case O
--   - reading: M, v̄_o, Q_o unspecified positive sizes; p_m a price; c_E^r with no stated sign → real M, v̄_o, Q_o > 0, p_m ≥ 0, c_E^r ≥ 0 (fields of Params), with k > 0, δ_o ∈ [0,1), ρ_p ∈ (0,1] as printed; reason: sizes, a price and a value; v̄_o is the upper end of a uniform law; M is real as in the paper, which differentiates in M
-- source:
--   Baron–Romero–Zhang–Zhou, Innovative Business Models in Ocean-Bound Plastic Recycling, MSOM, doi:10.1287/msom.2022.0643, Proposition 2(a), p.15; Assumption 1, p.15

import Mathlib
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark
import Definitions.Def_OceanPlastic_CaseO
import Definitions.Def_OceanPlastic_Problem4

namespace OceanPlastic

open Params

/-- **Proposition 2(a): problem (4) reduces to a concave univariate problem.**
Baron–Romero–Zhang–Zhou, MSOM, doi:10.1287/msom.2022.0643, Proposition 2(a), p. 15, under
Assumption 1(1)–(2), p. 15.

With non-negative weights `ρ₂, ρ₃`, `ρ₁ > max {ρ₂, ρ₃}` and
`δ_o ≤ √(M v̄_o (2ρ₁ − (1 + ρ_p) ρ₂) / (ρ₁ k Q_o))`, and with
`φ(r) = T^O(d^O_o(r), r)`:
* for every `r ≥ 0`, `d^O_o(r)` is feasible and is the unique maximizer of `d ↦ T^O(d, r)` among the
  `d` with `(r, d)` feasible;
* `(r, d)` is optimal for (4) iff `r ≥ 0`, `d = d^O_o(r)` and `r` maximizes `φ` over `[0, ∞)`;
* `φ` is concave on `[0, ∞)`;
* an optimal solution of (4) exists.

**Formalization Note** "The univariate convex optimization problem `r^O = arg max`" is stated as the
characterization of the second bullet together with concavity of `φ`, with no uniqueness claim: at
equality in Assumption 1(2), `φ` can be affine on a piece. Assumption 1(3) concerns Case S only. -/
theorem proposition_2a (P : Params) (ρ₁ ρ₂ ρ₃ : ℝ) (hρ₂ : 0 ≤ ρ₂) (hρ₃ : 0 ≤ ρ₃)
    (hA1 : max ρ₂ ρ₃ < ρ₁)
    (hA2 : P.δ ≤ Real.sqrt (P.M * P.vbar * (2 * ρ₁ - (1 + P.ρp) * ρ₂) / (ρ₁ * P.k * P.Q))) :
    (∀ r : ℝ, 0 ≤ r → P.Feasible r (P.dO r) ∧
      ∀ d : ℝ, P.Feasible r d → d ≠ P.dO r → P.TO ρ₁ ρ₂ ρ₃ d r < P.TO ρ₁ ρ₂ ρ₃ (P.dO r) r) ∧
    (∀ r d : ℝ, P.IsOptimal ρ₁ ρ₂ ρ₃ r d ↔
      0 ≤ r ∧ d = P.dO r ∧
        ∀ r' : ℝ, 0 ≤ r' → P.TO ρ₁ ρ₂ ρ₃ (P.dO r') r' ≤ P.TO ρ₁ ρ₂ ρ₃ (P.dO r) r) ∧
    ConcaveOn ℝ (Set.Ici 0) (fun r : ℝ => P.TO ρ₁ ρ₂ ρ₃ (P.dO r) r) ∧
    (∃ r d : ℝ, P.IsOptimal ρ₁ ρ₂ ρ₃ r d) := by sorry

end OceanPlastic
