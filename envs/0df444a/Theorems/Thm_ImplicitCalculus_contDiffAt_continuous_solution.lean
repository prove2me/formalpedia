-- Prove2me | Theorems.Thm_ImplicitCalculus_contDiffAt_continuous_solution
-- name    : ImplicitCalculus.contDiffAt_continuous_solution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T19:52:21.917234+00:00
-- url     : https://prove2.me/theorems/e0e88c94-ee88-496b-a644-f4dd6fac4d9e
-- title:
--   Smoothness of a supplied continuous implicit solution
-- statement:
--   Let E, G and F be Banach spaces over the real or complex scalars, and let n be any nonzero smoothness order supported by ContDiff. Suppose f:E×G→F is Cⁿ at (u,r(u)), the supplied solution r:E→G is continuous at u, and the derivative of f in the G variable there is invertible. If f(x,r(x))=f(u,r(u)) for all x sufficiently near u, then r is Cⁿ at u. This applies to a given continuous solution, rather than assuming it is the implicit function constructed by the inverse function theorem.
-- source:
--   Generalization of smoothContinuousImplicitSolution in Solutions/Sol_BirkhoffGlobalSection_smooth_radial_gauge_chart.lean:9. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Analysis/Calculus/ImplicitContDiff.lean, ContDiffAt.contDiffAt_implicitFunction and ContDiffAt.eventually_apply_eq_iff_implicitFunction. https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/ImplicitContDiff.lean. This is a corollary for supplied solutions, not a new implicit function existence theorem.

import Mathlib.Analysis.Calculus.ImplicitContDiff

open Filter
open scoped Topology ContDiff
set_option autoImplicit false

theorem ImplicitCalculus.contDiffAt_continuous_solution {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (n : ℕ∞ω) (hn : n ≠ 0) (f : E × G → F) (r : E → G) (u : E)
    (hf : ContDiffAt 𝕜 n f (u, r u)) (hr : ContinuousAt r u)
    (hi : ((fderiv 𝕜 f (u, r u)).comp
      (ContinuousLinearMap.inr 𝕜 E G)).IsInvertible)
    (heq : ∀ᶠ x in 𝓝 u, f (x, r x) = f (u, r u)) :
    ContDiffAt 𝕜 n r u := by sorry
