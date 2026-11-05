-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_compressed_norm_eq_on_minimal_family
-- name    : OAI.BoundedHochschild.KadisonRingrose.compressed_norm_eq_on_minimal_family
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:02.28766+00:00
-- url     : https://prove2.me/theorems/0011afe0-4d14-43dd-8856-fe36ce8185f4
-- title:
--   Compressed norms are constant on a minimal family of represented averages
-- statement:
--   Let $M$ be a unital C*-algebra, $H,K$ complex Hilbert spaces, and $\pi:M\to B(K)$, $\sigma:M\to B(H)$ unital *-homomorphisms. For $m=(m_i)$ finite with $\sum_i m_im_i^*=1$, the represented right average of an operator $W:H\to K$ is $\sum_i\pi(m_i)W\sigma(m_i)^*$ (`representedRightAverage`). Let $F$ be a set of operators $H\to K$, closed in the weak operator topology, convex, invariant under all represented right averages (`RepresentedRightAverageInvariant`), and minimal among nonempty subsets with these properties. If $P\in B(K)$ commutes with $\pi(M)$ and $Q\in B(H)$ commutes with $\sigma(M)$, then
--
--   $$\|PUQ\|=\|PVQ\|\qquad\text{for all }U,V\in F.$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.compressed_norm_eq_on_minimal_family`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/CompressedAveragingNorms.lean#L61

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem compressed_norm_eq_on_minimal_family (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Set (H →WOT[ℂ] K))
    (hclosed : IsClosed F) (hconv : Convex ℝ F)
    (hinv : RepresentedRightAverageInvariant π σ F)
    (hmin : ∀ G : Set (H →WOT[ℂ] K), G ⊆ F → G.Nonempty → IsClosed G →
      Convex ℝ G → RepresentedRightAverageInvariant π σ G → F ⊆ G)
    (P : K →L[ℂ] K) (Q : H →L[ℂ] H)
    (hP : ∀ a, P.comp (π a) = (π a).comp P)
    (hQ : ∀ a, Q.comp (σ a) = (σ a).comp Q)
    {U V : H →WOT[ℂ] K} (hU : U ∈ F) (hV : V ∈ F) :
    ‖(weakCompression P Q U).toCLM‖ = ‖(weakCompression P Q V).toCLM‖ := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
