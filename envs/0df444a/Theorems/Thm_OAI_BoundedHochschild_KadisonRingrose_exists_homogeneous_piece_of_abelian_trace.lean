-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_homogeneous_piece_of_abelian_trace
-- name    : OAI.BoundedHochschild.KadisonRingrose.exists_homogeneous_piece_of_abelian_trace
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:09.898266+00:00
-- url     : https://prove2.me/theorems/43f0a7ca-76af-4d81-840e-03e8fd66bd0e
-- title:
--   A nonzero abelian projection yields a homogeneous type I central piece
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). Let $\tau$ be a positive functional on $M$ that is tracial and faithful, and let $p\ne0$ be an abelian projection. Then there is a nonzero central projection $z$ whose corner is homogeneous of type I (`HomogeneousTypeICorner z`): for some $n$ the corner $zMz$ has a matrix system of size $n$ with one abelian diagonal unit.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.exists_homogeneous_piece_of_abelian_trace`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/FiniteTypeIPieces.lean#L20

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners FinitePathMain

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_homogeneous_piece_of_abelian_trace
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hfaith : ∀ a : M, τ (star a * a) = 0 → a = 0)
    {p : M} (hp : AbelianProjection p) (hp0 : p ≠ 0) :
    ∃ z : M, CentralProjection z ∧ z ≠ 0 ∧ HomogeneousTypeICorner z := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
