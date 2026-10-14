-- Prove2me | Theorems.Thm_GarrettFA_continuous_linearMap_of_isInitTopology
-- name    : GarrettFA.continuous_linearMap_of_isInitTopology
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:39:54.293576+00:00
-- url     : https://prove2.me/theorems/397ccc0a-258b-42ec-8bcd-4c1a06a95ff3
-- title:
--   Claim 5.0.5 — every linear functional on $V_{\mathrm{init}}$ is continuous
-- statement:
--   Let $V$ be a vector space over $\mathbb K=\mathbb R$ or $\mathbb C$ whose (Hausdorff) topology is the topology of $V_{\rm init}$. Then every linear functional
--
--   $$\lambda : V\to\mathbb K$$
--
--   is continuous.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 8, Claim 5.0.5

import Definitions.Def_GarrettFA_IsInitTopology

namespace GarrettFA
theorem continuous_linearMap_of_isInitTopology {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    (hV : IsInitTopology 𝕜 V) (f : V →ₗ[𝕜] 𝕜) :
    Continuous f := by sorry
end GarrettFA
