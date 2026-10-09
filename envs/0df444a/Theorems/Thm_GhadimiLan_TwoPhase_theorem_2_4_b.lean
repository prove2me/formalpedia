-- Prove2me | Theorems.Thm_GhadimiLan_TwoPhase_theorem_2_4_b
-- name    : GhadimiLan.TwoPhase.theorem_2_4_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:41.956986+00:00
-- url     : https://prove2.me/theorems/e16eb0db-44fe-4d0b-8d01-1e139506304b
-- title:
--   Theorem 2.4(b) — two-phase RSG finds an (ε, Λ)-solution
-- statement:
--   Consider the two-phase RSG method of Theorem 2.4. Let $\varepsilon>0$ and $0<\Lambda<1$, and set
--
--   $$S=\left\lceil\log_2(2/\Lambda)\right\rceil,\qquad N=\left\lceil\max\left\{\frac{32L^2D_f^2}{\varepsilon},\left[\frac{32L(\widetilde D+D_f^2/\widetilde D)\sigma}{\varepsilon}\right]^2\right\}\right\rceil,\qquad T=\left\lceil\frac{24(S+1)\sigma^2}{\Lambda\varepsilon}\right\rceil.$$
--
--   The selected candidate $\bar x^*$ is an $(\varepsilon,\Lambda)$-solution:
--
--   $$\Pr\{\|\nabla f(\bar x^*)\|^2\le\varepsilon\}\ge1-\Lambda.$$
--
--   The algorithm uses at most $S(N+T)$ stochastic first-order oracle calls: $S$ runs of at most $N$ calls, followed by $T$ estimates for each candidate.
--
--   **Formalization Note** The call count follows from the modeled loops and is stated in prose rather than through a separate call-counting semantics. The logarithm in (2.24) is read in base two; the printed proof's $2^{-S}\le\Lambda/2$ does not follow from a natural logarithm. The model has $\sigma>0$, since otherwise (2.13) and (2.26) yield a zero step or zero sample size in Lean.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Theorem 2.4(b), Eqs. (2.24)–(2.27), p. 12

import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Theorem 2.4(b), Eqs. (2.24)–(2.27), p. 12. The logarithm in (2.24)
is read in base two, as required by the paper's final 2⁻ˢ bound. -/
theorem theorem_2_4_b {n S N T : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n Ξ) (A : System (S := S) (N := N) (T := T) P μ)
    (ε Λ : ℝ) (hε : 0 < ε) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1)
    (hS : S = Nat.ceil (Real.logb 2 (2 / Λ)))
    (hN : N = Nat.ceil (max (32 * P.L ^ 2 * Df P ^ 2 / ε)
      ((32 * P.L * (P.Dt + Df P ^ 2 / P.Dt) * P.σ / ε) ^ 2)))
    (hT : T = Nat.ceil (24 * ((S : ℝ) + 1) * P.σ ^ 2 / (Λ * ε))) :
    ENNReal.ofReal (1 - Λ) ≤
      μ {ω | ‖P.g (chosen A ω)‖ ^ 2 ≤ ε} := by sorry

end GhadimiLan.TwoPhase
