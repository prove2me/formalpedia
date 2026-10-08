-- Prove2me | Theorems.Thm_KernelDRO_Duality_lemma_D_2
-- name    : KernelDRO.Duality.lemma_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:43.49235+00:00
-- url     : https://prove2.me/theorems/80895e0e-8363-46a2-a35e-660c16279768
-- title:
--   Lemma D.2, p. 23 — the image $\mathcal T(\mathcal P)$ of the mean map is compact
-- statement:
--   Let $\mathcal X$ be a compact metric space with its Borel $\sigma$-algebra and $\varphi:\mathcal X\to\mathcal H$ a continuous feature map into a real Hilbert space. The image of the set of Borel probability measures under the mean map $\mathcal T:P\mapsto\mu_P=\int\varphi\,dP$,
--   $$\mathcal T(\mathcal P)=\{\mu_P: P\in\mathcal P\}\subseteq\mathcal H,$$
--   is compact. It is the set of all achievable mean embeddings, and its compactness underlies the compactness of the ambiguity set.
--
--   **Formalization Note** The paper's proof uses that $\mathcal T$ is an isometry for a universal kernel; the statement only needs $\varphi$ continuous.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, §D.2, Lemma D.2, p. 23

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **Lemma D.2** (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization,
arXiv:2006.06981v3, Lemma D.2, p. 23). The image `𝒯(𝒫) = {µ_P | P ∈ 𝒫} ⊆ ℋ` of the set of Borel
probability measures under the mean map `𝒯 : P ↦ µ_P` is compact if `𝒳` is compact.

**Formalization Note.** `𝒳` is a compact metric space with its Borel σ-algebra and `φ` is
continuous. The paper's proof calls `𝒯` an isometry from `(𝒫, MMD)`, which needs a universal kernel;
the statement itself does not mention the metric on `𝒫`, so nothing is lost by assuming only that
`φ` is continuous. -/
theorem lemma_D_2 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) :
    IsCompact (Set.range (meanEmbedding φ)) := by sorry

end KernelDRO.Duality
