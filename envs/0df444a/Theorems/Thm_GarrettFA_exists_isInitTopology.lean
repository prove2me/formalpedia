-- Prove2me | Theorems.Thm_GarrettFA_exists_isInitTopology
-- name    : GarrettFA.exists_isInitTopology
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:38:59.640096+00:00
-- url     : https://prove2.me/theorems/25efe4af-bf4c-4617-b004-24ad49e7e960
-- title:
--   §5 — existence of the finest locally convex topology $V_{\mathrm{init}}$
-- statement:
--   Every vector space $V$ over $\mathbb K=\mathbb R$ or $\mathbb C$ carries a Hausdorff topological vector space topology that is the topology of $V_{\rm init}$, the locally convex colimit of its finite-dimensional subspaces.
--
--   This guarantees that the predicate describing $V_{\rm init}$ is not vacuous.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 8, §5 ("V_init = locally-convex colimit of finite-dimensional X ⊂ V"; existence of locally convex colimits, §1)

import Definitions.Def_GarrettFA_IsInitTopology

namespace GarrettFA
theorem exists_isInitTopology {𝕜 : Type*} [RCLike 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] [Module ℝ V] [IsScalarTower ℝ 𝕜 V] :
    ∃ τ : TopologicalSpace V, @IsTopologicalAddGroup V τ _ ∧ @ContinuousSMul 𝕜 V _ _ τ ∧
      @T2Space V τ ∧ @IsInitTopology 𝕜 V _ _ _ _ _ τ := by sorry
end GarrettFA
