-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_hasWeakDerivAlong_of_sq_difference_le_readable
-- name    : FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_sq_difference_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:14.391461+00:00
-- url     : https://prove2.me/theorems/75fca118-0385-4fa0-a865-9c9b02ff0dda
-- title:
--   Weak Derivative From an L2 Difference Bound
-- statement:
--   This formalizes the difference-quotient criterion associated with Nirenberg and Evans, PDE §5.8.2, Theorem 3(ii).
--
--   Let $E$ be a finite-dimensional real inner-product normed space, let $f\in L^2(\operatorname{vol})$, and fix $v\in E$. Suppose there is $C\in\mathbb R$ such that for every nonzero $t\in\mathbb R$ with $|t|\le1$,
--   $$\int_E\bigl(f(x+tv)-f(x)\bigr)^2\,d\operatorname{vol}(x)\le Ct^2.$$
--
--   Then there exists $g\in L^2(\operatorname{vol})$ such that $g$ is a weak derivative of $f$ along $v$.
--
--   The theorem is an $L^2$ existence criterion; it does not identify the derivative uniquely by an explicit pointwise formula.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_hasWeakDerivAlong_of_sq_difference_le
--       {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E)) (v : E) {C : ℝ}
--       (hdiff : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
--         ∫ x, (f (x + t • v) - f x) ^ 2 ∂(volume : Measure E) ≤ C * t ^ 2) :
--       ∃ g : E → ℝ, HasWeakDerivAlong f g v ∧ MemLp g 2 (volume : Measure E)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Mollification`](https://prove2.me/theorems/480cb5f8-8cac-4e12-bd32-870acaf66221).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`quotient_pairing_tendsto`](https://prove2.me/theorems/93835bcb-bdbc-4706-adbe-19b48ce839be).
--
--   Previous: [`quotient_pairing_tendsto`](https://prove2.me/theorems/93835bcb-bdbc-4706-adbe-19b48ce839be).
--
--   [Source excerpt, lines 189–193](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Mollification.lean#L189-L193) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Mollification.lean#L186-L269 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Mollification`, declaration `FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_sq_difference_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Mollification

open MeasureTheory Set Filter
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]

theorem FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_sq_difference_le_readable
    {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E)) (v : E) {C : ℝ}
    (hdiff : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      ∫ x, (f (x + t • v) - f x) ^ 2 ∂(volume : Measure E) ≤ C * t ^ 2) :
    ∃ g : E → ℝ, HasWeakDerivAlong f g v ∧ MemLp g 2 (volume : Measure E) := by sorry
