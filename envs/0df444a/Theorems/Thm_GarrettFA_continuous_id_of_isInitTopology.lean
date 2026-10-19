-- Prove2me | Theorems.Thm_GarrettFA_continuous_id_of_isInitTopology
-- name    : GarrettFA.continuous_id_of_isInitTopology
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T19:39:26.648933+00:00
-- url     : https://prove2.me/theorems/1775ebcc-6e94-4053-a21e-2f12f789499d
-- title:
--   Claim 5.0.4 — $V_{\mathrm{init}}$ is the finest locally convex topology
-- statement:
--   Let $V$ be a vector space over $\mathbb K=\mathbb R$ or $\mathbb C$ whose (Hausdorff) topology is the topology of $V_{\rm init}$. Let $\tau$ be any locally convex topological vector space topology on $V$. Then
--
--   $$\mathrm{id} : V_{\rm init} \to (V,\tau) \ \text{ is continuous},$$
--
--   so $V_{\rm init}$ is the finest locally convex topological vector space topology on $V$.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 8, Claim 5.0.4

import Definitions.Def_GarrettFA_IsInitTopology

namespace GarrettFA
theorem continuous_id_of_isInitTopology {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] (τ : TopologicalSpace V) (h₁ : @IsTopologicalAddGroup V τ _)
    (h₂ : @ContinuousSMul 𝕜 V _ _ τ) (h₃ : @LocallyConvexSpace ℝ V _ _ _ _ τ)
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [T2Space V]
    (hV : IsInitTopology 𝕜 V) :
    @Continuous V V _ τ id := by sorry
end GarrettFA
