-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_normalGNS_nontrivial
-- name    : OAI.BoundedHochschild.KadisonRingrose.normalGNS_nontrivial
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:12.269222+00:00
-- url     : https://prove2.me/theorems/99501397-bf77-47f7-b509-390102f029ac
-- title:
--   The normal GNS space of a nontrivial von Neumann algebra is nontrivial
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). The normal GNS space `NormalGNS e` is the subspace of normal vectors of the universal GNS representation of $M$. If $M$ is nontrivial, then `NormalGNS e` is nontrivial.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.normalGNS_nontrivial`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/RepresentedRightAverages.lean#L19

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem normalGNS_nontrivial [Nontrivial M] (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Nontrivial (NormalGNS e) := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
