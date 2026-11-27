-- Prove2me | Theorems.Thm_FracRiccati_Radius_Supplement_theorem_3_3_b_positive
-- name    : FracRiccati.Radius.Supplement.theorem_3_3_b_positive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:54:15.597648+00:00
-- url     : https://prove2.me/theorems/d3883429-b0cb-4807-9593-b6899afa6150
-- title:
--   Theorem 3.3(b), positive Moreover clause — monotonicity, blow-up and noncontinuation
-- statement:
--   Let $0<\alpha\le2$ and let real $\lambda,\nu>0$, $\mu\ge0$. Write $R$ for the published Hadamard radius of the coefficients (3.19), and $\psi$ for their fractional power-series sum. Then
--   $$0<R<\infty,\qquad \psi\text{ is strictly increasing on }[0,R),\qquad \lim_{t\uparrow R}\psi(t)=+\infty.$$
--   Moreover, there is no real-valued function continuous at $R$ agreeing with $\psi$ throughout $[0,R)$. This gives the claimed obstruction to continuation across the finite endpoint; no maximal-solution theory is being assumed.
--
--   Differences from the source:
--   - encoding: the printed order interval includes zero → the order is strictly positive and at most two; reason: the radius exponent contains division by the order, so zero is undefined
--   - reading: increasing on the series domain → strictly increasing on [0,R); reason: the first coefficient is positive and the remaining coefficients are nonnegative; the brief requests the strict reading
--   - reading: existence domain [0,R) → no continuous extension across R; reason: this is the endpoint obstruction implied by blow-up, rather than an additional maximal-solution formalism
--   - encoding: a real series in the real-parameter case → the real part of the complex series and the finite ENNReal radius converted to a real endpoint; reason: the coefficients are real and the conclusion explicitly asserts a positive finite radius
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 9, Theorem 3.3(b), Moreover clause (λ, ν > 0, µ ≥ 0)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_Psi

namespace FracRiccati.Radius.Supplement

open Filter Topology

theorem theorem_3_3_b_positive (α l m n : ℝ)
    (hα : 0 < α) (hα2 : α ≤ 2) (hl : 0 < l) (hm : 0 ≤ m) (hn : 0 < n) :
    let R := radius α (coeff α l m n)
    0 < R ∧ R < ⊤ ∧
    StrictMonoOn (psiReal α l m n) (Set.Ico 0 R.toReal) ∧
    Tendsto (psiReal α l m n) (nhdsWithin R.toReal (Set.Ico 0 R.toReal)) atTop ∧
    (¬ ∃ f : ℝ → ℝ,
      ContinuousAt f R.toReal ∧ Set.EqOn f (psiReal α l m n) (Set.Ico 0 R.toReal)) := by sorry

end FracRiccati.Radius.Supplement
