-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_projection_defect_eq_zero
-- name    : OAI.BoundedHochschild.KadisonRingrose.projection_defect_eq_zero
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:40:48.030414+00:00
-- url     : https://prove2.me/theorems/b89e7d07-df11-4251-a3de-220c7779785d
-- title:
--   Vanishing of the projection defect for a factorized map
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). Let $\sigma$ be the normal GNS representation on $N=$ `NormalGNS e`, let $\pi:M\to B(K)$ be a unital *-homomorphism on a Hilbert space, and let $L,W:N\to K$ be bounded with $\sigma(T(a))=L^*\pi(a)W$ for a bounded linear $T:M\to M$. Suppose $\|W\sigma(f)\|=\|\pi(f)W\sigma(f)\|$ for every projection $f\in M$. Then for all $a\in M$ and every projection $p\in M$,
--
--   $$T(a)p-T(ap)p=0.$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.projection_defect_eq_zero`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/ProjectionDefectRigidity.lean#L22

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem projection_defect_eq_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L W : NormalGNS e →L[ℂ] K)
    (T : M →L[ℂ] M)
    (hT : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W))
    (hnorm : ∀ f : M, IsStarProjection f →
      ‖W.comp (normalGNSRepresentation e f)‖ =
        ‖(π f).comp (W.comp (normalGNSRepresentation e f))‖)
    (a : M) {p : M} (hp : IsStarProjection p) : T a * p - T (a * p) * p = 0 := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
