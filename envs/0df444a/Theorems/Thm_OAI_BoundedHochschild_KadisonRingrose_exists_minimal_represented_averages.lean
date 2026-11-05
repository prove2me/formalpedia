-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_minimal_represented_averages
-- name    : OAI.BoundedHochschild.KadisonRingrose.exists_minimal_represented_averages
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:43.675167+00:00
-- url     : https://prove2.me/theorems/294a4f07-68c5-425b-b1a5-633bca9c8653
-- title:
--   Existence of a minimal invariant family of represented averages
-- statement:
--   Let $M$ be a unital C*-algebra, $H,K$ complex Hilbert spaces, $\pi:M\to B(K)$, $\sigma:M\to B(H)$ unital *-homomorphisms and $W:H\to K$ a bounded operator. Let $\mathcal O(W)$ be the weak-operator closure of the set of represented right averages $\sum_i\pi(m_i)W\sigma(m_i)^*$ with $\sum_im_im_i^*=1$ (`closedRepresentedAveragingOrbit`). Then $\mathcal O(W)$ contains a nonempty set $F$ that is weak-operator closed, convex, invariant under all represented right averages, and contained in every nonempty closed convex invariant subset of itself.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.exists_minimal_represented_averages`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/MinimalRepresentedAverages.lean#L24

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_minimal_represented_averages (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    ∃ F : Set (H →WOT[ℂ] K), F ⊆ closedRepresentedAveragingOrbit π σ W ∧
      F.Nonempty ∧ IsClosed F ∧ Convex ℝ F ∧ RepresentedRightAverageInvariant π σ F ∧
      ∀ G : Set (H →WOT[ℂ] K), G ⊆ F → G.Nonempty → IsClosed G →
        Convex ℝ G → RepresentedRightAverageInvariant π σ G → F ⊆ G := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
