-- Prove2me | Theorems.Thm_ImplicitCalculus_smooth_level_parametrization
-- name    : ImplicitCalculus.smooth_level_parametrization
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T16:35:41.943649+00:00
-- url     : https://prove2.me/theorems/0a0d4782-639d-401e-945b-8cd296843672
-- title:
--   Smooth local level parametrization with derivative the tangent inclusion
-- statement:
--   Let V be a real Banach space and W a finite-dimensional real normed space. Suppose F from V to W is smooth at y and DF at y is surjective. Write K for its kernel. There exists a map gamma from K into V, smooth at zero, such that
--
--   $$\gamma(0)=y,\qquad D\gamma_0:K\hookrightarrow V,\qquad F(\gamma(z))=F(y)\quad\text{for all z near zero}.$$
--
--   The derivative is the canonical kernel inclusion. This is a local level parametrization; compactness, global regularity, contact forms, and a finite-dimensional source are unnecessary.
-- source:
--   Smooth implicit-function theorem. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/ImplicitContDiff.lean, ImplicitFunctionData.contDiffAt_implicitFunction; Implicit.lean, to_implicitFunctionOfComplemented and map_implicitFunctionOfComplemented_eq.

import Mathlib.Analysis.Calculus.ImplicitContDiff

set_option autoImplicit false
open Filter
open scoped ContDiff Topology

theorem ImplicitCalculus.smooth_level_parametrization
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (F : V → W) (y : V) (hF : ContDiffAt ℝ ∞ F y)
    (hD : Function.Surjective (fderiv ℝ F y)) :
    ∃ γ : (fderiv ℝ F y).ker → V,
      ContDiffAt ℝ ∞ γ 0 ∧ γ 0 = y ∧
      HasFDerivAt γ (fderiv ℝ F y).ker.subtypeL 0 ∧
      ∀ᶠ z in 𝓝 (0 : (fderiv ℝ F y).ker), F (γ z) = F y := by sorry
