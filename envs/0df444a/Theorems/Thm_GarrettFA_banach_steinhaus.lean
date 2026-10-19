-- Prove2me | Theorems.Thm_GarrettFA_banach_steinhaus
-- name    : GarrettFA.banach_steinhaus
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T19:29:55.525986+00:00
-- url     : https://prove2.me/theorems/93fb60d3-08aa-4ad3-8047-8f795334abe0
-- title:
--   Thm. 3.0.1 — Banach–Steinhaus for Fréchet and LF-spaces
-- statement:
--   Let $X$ be a Fréchet space or an LF-space and $Y$ a locally convex topological vector space over $\mathbb K=\mathbb R$ or $\mathbb C$. Let $E$ be a set of continuous linear maps $X\to Y$ such that for every $x\in X$ the orbit
--
--   $$E x=\{\,Tx : T\in E\,\}$$
--
--   is bounded in $Y$. Then $E$ is equicontinuous.
--
--   This uniform boundedness principle is what makes pointwise limits of operators continuous in Theorem 4.1.1.
--
--   **Formalization Note** The notes say "a set $E$ of linear maps". The statement is false for discontinuous maps: a single discontinuous linear functional on a Banach space has bounded orbits but is not equicontinuous. The proof in the notes uses closedness of $T^{-1}U$, so continuity of the maps is assumed here.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 4, Theorem 3.0.1 (with continuity of the maps, which the proof uses)

import Definitions.Def_GarrettFA_IsEquicontinuousSet
import Definitions.Def_GarrettFA_IsFrechetSpace
import Definitions.Def_GarrettFA_IsLFSpace

namespace GarrettFA
theorem banach_steinhaus {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    (hX : IsFrechetSpace 𝕜 X ∨ IsLFSpace 𝕜 X)
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y] [IsScalarTower ℝ 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [LocallyConvexSpace ℝ Y]
    [T2Space Y]
    (E : Set (X →L[𝕜] Y))
    (hE : ∀ x : X, Bornology.IsVonNBounded 𝕜 ((fun T : X →L[𝕜] Y => T x) '' E)) :
    IsEquicontinuousSet ((fun T : X →L[𝕜] Y => (T : X → Y)) '' E) := by sorry
end GarrettFA
