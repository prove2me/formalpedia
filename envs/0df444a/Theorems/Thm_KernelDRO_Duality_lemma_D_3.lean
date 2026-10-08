-- Prove2me | Theorems.Thm_KernelDRO_Duality_lemma_D_3
-- name    : KernelDRO.Duality.lemma_D_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:33.841827+00:00
-- url     : https://prove2.me/theorems/afd8967f-c050-462a-a8b1-afa3e399267f
-- title:
--   Lemma D.3, p. 23 — $\mathcal C_{\mathcal P}=\mathcal C\cap\mathcal T(\mathcal P)$ is compact
-- statement:
--   Let $\mathcal X$ be a compact metric space with its Borel $\sigma$-algebra, $\varphi:\mathcal X\to\mathcal H$ continuous, and $\mathcal C\subseteq\mathcal H$ closed and convex (the clauses of Assumption 3.1 on $\mathcal C$). Then
--   $$\mathcal C_{\mathcal P}=\mathcal C\cap\mathcal T(\mathcal P)=\{\mu\in\mathcal C:\ \mu=\mu_P\text{ for some }P\in\mathcal P\}$$
--   is compact.
--
--   **Formalization Note** The clauses of Assumption 3.1 on the loss and the Slater clause do not enter this statement and are omitted.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, §D.2, Lemma D.3, p. 23

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **Lemma D.3** (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization,
arXiv:2006.06981v3, Lemma D.3, p. 23). Let `𝒞_𝒫 = 𝒞 ∩ 𝒯(𝒫)`, where `𝒯(𝒫) = {µ_P | P ∈ 𝒫}`. If `𝒳`
is compact, under Assumption 3.1 (`𝒞` closed and convex), `𝒞_𝒫` is compact.

**Formalization Note.** `𝒳` is a compact metric space with its Borel σ-algebra and `φ` is
continuous. Of Assumption 3.1 (p. 3) only the clauses on `𝒞` concern this statement; the clauses on
the loss and the Slater clause do not appear in it and are omitted. -/
theorem lemma_D_3 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (C : Set H) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) :
    IsCompact (C ∩ Set.range (meanEmbedding φ)) := by sorry

end KernelDRO.Duality
