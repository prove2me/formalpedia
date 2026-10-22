-- Prove2me | Theorems.Thm_LieSuperCStar_Correspondence_theorem_6_4
-- name    : LieSuperCStar.Correspondence.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:59.49467+00:00
-- url     : https://prove2.me/theorems/8d22f7e8-9467-48b9-a3a3-5752ba29150a
-- title:
--   Theorem 6.4, p. 13 — isomorphism of representation categories
-- statement:
--   For every finite-dimensional Lie supergroup $(G,\mathfrak g)$, the two constructions of Propositions 6.1 and 6.3 give an isomorphism between its category of unitary representations and the category of nondegenerate *-representations of $\mathcal A(G,\mathfrak g)$:
--
--   $$
--   \operatorname{URep}(G,\mathfrak g)\cong
--   \operatorname{Rep}_{\mathrm{nd}}(\mathcal A(G,\mathfrak g)).
--   $$
--
--   Each unitary representation has a unique corresponding nondegenerate algebra representation; each nondegenerate algebra representation has a unique corresponding unitary Lie supergroup representation; and a bounded even operator intertwines the two unitary representations exactly when it intertwines their algebra representations. The assignments keep the underlying Hilbert spaces and bounded morphisms.
--
--   **Formalization Note** The three clauses are written separately, with uniqueness in both object directions and an equivalence of intertwiner predicates. Agreement on represented word generators is the common correspondence predicate. Hilbert spaces range over `Type`; no connectedness or second countability is imposed.
-- source:
--   Neeb–Salmasian, C*-algebras and direct integral decomposition for Lie supergroups, arXiv:1506.01558v1, p. 13, Theorem 6.4; proof pp. 14–15

import Mathlib
import Definitions.Def_LieSuperCStar_Correspondence_Setting

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

namespace LieSuperCStar.Correspondence

/-- Theorem 6.4, p. 13: the two constructions are inverse on objects and on
    bounded even intertwiners. -/
theorem theorem_6_4
    {E G F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
    [Group G] [LieGroup 𝓘(ℝ, E) ∞ G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hc : HCPair E G F) (μ : Measure G) [μ.IsHaarMeasure] :
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : UnitaryRep hc H),
      ∃! Ψ : CStarAlg hc μ →⋆ₙₐ[ℂ] (H →L[ℂ] H),
        IsNondegenerate Ψ ∧ Corresponds π Ψ) ∧
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (Ψ : CStarAlg hc μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      IsNondegenerate Ψ → ∃! π : UnitaryRep hc H, Corresponds π Ψ) ∧
    (∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (π : UnitaryRep hc H) (σ : UnitaryRep hc K)
      (Ψ : CStarAlg hc μ →⋆ₙₐ[ℂ] (H →L[ℂ] H))
      (Φ : CStarAlg hc μ →⋆ₙₐ[ℂ] (K →L[ℂ] K))
      (T : H →L[ℂ] K),
      IsNondegenerate Ψ → IsNondegenerate Φ →
      Corresponds π Ψ → Corresponds σ Φ →
      (IsIntertwiner π σ T ↔ ∀ a : CStarAlg hc μ,
        T ∘L Ψ a = Φ a ∘L T)) := by sorry

end LieSuperCStar.Correspondence
