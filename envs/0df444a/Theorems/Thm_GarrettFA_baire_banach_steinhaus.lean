-- Prove2me | Theorems.Thm_GarrettFA_baire_banach_steinhaus
-- name    : GarrettFA.baire_banach_steinhaus
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:30:31.939977+00:00
-- url     : https://prove2.me/theorems/68a0024a-1ac1-487b-b3a1-245823b1e590
-- title:
--   Remark 3.0.2 — Baire-category form of Banach–Steinhaus
-- statement:
--   Let $X$ be a topological vector space and $Y$ a locally convex topological vector space over $\mathbb K=\mathbb R$ or $\mathbb C$, and let $E$ be a set of continuous linear maps $X\to Y$. Put
--
--   $$B_E=\{\,x\in X : E x \text{ is bounded in } Y\,\}.$$
--
--   If $B_E$ is not meagre (not a countable union of nowhere dense sets), then $B_E=X$ and $E$ is equicontinuous.
--
--   No completeness or metrizability of $X$ is assumed. Theorem 3.0.1 for Fréchet spaces follows, since Fréchet spaces are Baire spaces.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 5, Remark 3.0.2

import Definitions.Def_GarrettFA_IsEquicontinuousSet

namespace GarrettFA
theorem baire_banach_steinhaus {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y] [IsScalarTower ℝ 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [LocallyConvexSpace ℝ Y]
    [T2Space Y]
    (E : Set (V →L[𝕜] Y))
    (hE : ¬ IsMeagre {x : V | Bornology.IsVonNBounded 𝕜 ((fun T : V →L[𝕜] Y => T x) '' E)}) :
    {x : V | Bornology.IsVonNBounded 𝕜 ((fun T : V →L[𝕜] Y => T x) '' E)} = Set.univ ∧
      IsEquicontinuousSet ((fun T : V →L[𝕜] Y => (T : V → Y)) '' E) := by sorry
end GarrettFA
