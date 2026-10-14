-- Prove2me | Theorems.Thm_GarrettFA_isEquicontinuousSet_iff_of_isStrictColimit
-- name    : GarrettFA.isEquicontinuousSet_iff_of_isStrictColimit
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:29:14.414701+00:00
-- url     : https://prove2.me/theorems/51723958-9375-4b54-9ce3-9497cd68c344
-- title:
--   Prop. 2.2.1 — equicontinuity on strict colimits
-- statement:
--   Let $V$ be the strict colimit of a chain of closed subspaces $V_0\subsetneq V_1\subsetneq\cdots$ (over $\mathbb K=\mathbb R$ or $\mathbb C$), let $Y$ be a locally convex topological vector space, and let $E$ be a set of continuous linear maps $V\to Y$. Then
--
--   $$E \text{ is equicontinuous} \iff \text{for every } i,\ \{T|_{V_i} : T\in E\} \text{ is equicontinuous}.$$
--
--   Equicontinuity on an LF-space can therefore be checked on its Fréchet steps. This is how Banach–Steinhaus passes from Fréchet spaces to LF-spaces.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 4, Proposition 2.2.1

import Definitions.Def_GarrettFA_IsStrictColimit
import Definitions.Def_GarrettFA_IsEquicontinuousSet

namespace GarrettFA
theorem isEquicontinuousSet_iff_of_isStrictColimit {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V] {F : ℕ → Submodule 𝕜 V} (hF : IsStrictColimit 𝕜 F)
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y] [IsScalarTower ℝ 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [LocallyConvexSpace ℝ Y]
    [T2Space Y]
    (E : Set (V →L[𝕜] Y)) :
    IsEquicontinuousSet ((fun T : V →L[𝕜] Y => (T : V → Y)) '' E) ↔
      ∀ i, IsEquicontinuousSet ((fun T : V →L[𝕜] Y => fun y : F i => T y) '' E) := by sorry
end GarrettFA
