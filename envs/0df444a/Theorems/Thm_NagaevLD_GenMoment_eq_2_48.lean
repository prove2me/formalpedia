-- Prove2me | Theorems.Thm_NagaevLD_GenMoment_eq_2_48
-- name    : NagaevLD.GenMoment.eq_2_48
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:38.858393+00:00
-- url     : https://prove2.me/theorems/3b204c76-d8e9-46f9-a102-e365532ab2ac
-- title:
--   (2.48), p. 768 — ∫_{u<0} e^{hu} dF_j(u) ≤ exp{g(0) + hx/n − g(x/n)} ∫_{u<0} e^{hu} dF_j(u), h = g′(x/n)
-- statement:
--   Let $X_j$ be a real random variable with distribution function $F_j$. Let $g:\mathbb R\to\mathbb R$ have, on $[0,\infty)$, a positive nondecreasing derivative $g'$, let $n\ge 1$ be an integer, $x>0$, and $h=g'(x/n)$. Then
--   $$\int_{-\infty}^{0-}e^{hu}\,dF_j(u)\ \le\ \exp\{g(0)+hx/n-g(x/n)\}\int_{-\infty}^{0-}e^{hu}\,dF_j(u).$$
--
--   The factor $\exp\{g(0)+hx/n-g(x/n)\}$ is at least $1$, so the negative part of $Ee^{hX_j}$ can be multiplied by it; this is what makes $b_j(x/n)$, rather than the bare integral, appear in the per-summand bound of Theorem 2.5.
--
--   **Formalization Note** $\int_{-\infty}^{0-}$ is the integral over the event $\{X_j<0\}$. Since $h>0$ the integrand lies in $(0,1]$ there, so the integral is finite and no integrability hypothesis is needed. The hypotheses on $g$ are imposed on $[0,\infty)$ only. The implicit $n\ge1$ of the paper is explicit in Lean.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 768, proof of Theorem 2.5, (2.48)

import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- (2.48), p. 768: for `h = g′(x/n)`,
`E[e^{hX_j}; X_j < 0] ≤ exp{g(0) + hx/n − g(x/n)} · E[e^{hX_j}; X_j < 0]`. -/
theorem eq_2_48 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j))
    (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0)) (j : Fin n) (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    ∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P
      ≤ Real.exp (g 0 + h * (x / n) - g (x / n))
          * ∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P := by sorry

end NagaevLD.GenMoment
