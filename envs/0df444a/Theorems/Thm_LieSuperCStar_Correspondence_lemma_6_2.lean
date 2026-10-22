-- Prove2me | Theorems.Thm_LieSuperCStar_Correspondence_lemma_6_2
-- name    : LieSuperCStar.Correspondence.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:48.109785+00:00
-- url     : https://prove2.me/theorems/e03459de-65fc-45b3-957e-f1b0ea7f51ae
-- title:
--   Lemma 6.2, p. 11 — smooth vectors equal the represented algebraic core
-- statement:
--   Let $\Psi:\mathcal A(G,\mathfrak g)\to B(\mathcal H)$ be nondegenerate. Its multiplier extension produces a unitary group representation $U$ on $\mathcal H$. Let $\mathcal H^\circ$ be the linear span of $\Psi(\mathcal A^\circ)\mathcal H$. Then $U$ is strongly continuous and
--
--   $$
--   \mathcal H^\infty(U)=\mathcal H^\circ.
--   $$
--
--   This identifies the exact domain on which the odd infinitesimal operators are reconstructed. Smoothness on $G$ is equivalent to smoothness on $G_\varepsilon$, since the added parity action is bounded on a discrete factor.
--
--   **Formalization Note** The multiplier equation is included with an existential image element for each $g$ and $a$, so the characterization cannot hold vacuously if a translate failed to land in $\mathcal A$.
-- source:
--   Neeb–Salmasian, C*-algebras and direct integral decomposition for Lie supergroups, arXiv:1506.01558v1, pp. 11–12, Lemma 6.2 and equations (18)–(20)

import Mathlib
import Definitions.Def_LieSuperCStar_Correspondence_Setting

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

namespace LieSuperCStar.Correspondence

/-- Lemma 6.2, p. 11: exactly the represented algebraic core is smooth. -/
theorem lemma_6_2
    {E G F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
    [Group G] [LieGroup 𝓘(ℝ, E) ∞ G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hc : HCPair E G F) (μ : Measure G) [μ.IsHaarMeasure]
    (Ψ : CStarAlg hc μ →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hΨ : IsNondegenerate Ψ) :
    ∃ U : G →* (H ≃ₗᵢ[ℂ] H),
      IsMultExt Ψ U ∧
      (∀ v : H, Continuous (fun g : G => U g v)) ∧
      ∀ v : H,
        (QAlgorithms.Papers.Independent.Renew46.P09.HasSmoothOrbit
          (E := E) (fun g : G => U g) v ↔ v ∈ CoreVectors Ψ) := by sorry

end LieSuperCStar.Correspondence
