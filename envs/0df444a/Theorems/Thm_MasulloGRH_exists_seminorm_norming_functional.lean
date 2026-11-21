-- Prove2me | Theorems.Thm_MasulloGRH_exists_seminorm_norming_functional
-- name    : MasulloGRH.exists_seminorm_norming_functional
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-20T23:30:27.164282+00:00
-- url     : https://prove2.me/theorems/9322f5eb-2e4a-49c0-a30b-ffa65415099c
-- title:
--   Hahn–Banach norming functionals for continuous seminorms
-- statement:
--   Let $E$ be a complex locally convex topological vector space, let $p$ be a continuous seminorm on $E$, and let $x\in E$. There exists a continuous complex-linear functional $f$ on $E$ such that
--
--   $$|f(y)|\le p(y)\quad\text{for every }y\in E,\qquad |f(x)|=p(x).$$
--
--   No Hausdorffness or completeness is required. The result is a seminorm form of the Hahn–Banach norming-functional theorem. It identifies a continuous seminorm with the pointwise supremum of the absolute values of the continuous functionals it dominates.
--
--   This reusable helper is extracted from the direct proof of `MasulloGRH.frechet_equiv_subspace_bidual`, where it recovers the original topology from strong-bidual neighborhoods. It is also useful for dual descriptions of tensor seminorms.
-- source:
--   Hahn–Banach norming-functional theorem; derived using Mathlib exists_dual_vector'', Mathlib/Analysis/Normed/Module/HahnBanach.lean at commit 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Module/HahnBanach.lean. Extracted from the accepted proof https://prove2.me/theorems/d983b29e-b5c6-441b-9fb0-ed96f1a4966d, supporting the bidual step in Masullo Appendix C, Lemma C.2.4.11.

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH Topology

theorem MasulloGRH.exists_seminorm_norming_functional {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsLocallyConvexTopology E ‹TopologicalSpace E›)
    (p : Seminorm ℂ E) (hp : Continuous p) (x : E) :
    ∃ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ p y) ∧ ‖f x‖ = p x := by sorry
