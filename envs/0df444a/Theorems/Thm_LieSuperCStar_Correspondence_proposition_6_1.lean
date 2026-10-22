-- Prove2me | Theorems.Thm_LieSuperCStar_Correspondence_proposition_6_1
-- name    : LieSuperCStar.Correspondence.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:56.906984+00:00
-- url     : https://prove2.me/theorems/5e8fec41-5b2a-447a-a37d-0c80f52ac088
-- title:
--   Proposition 6.1, p. 11 — unique nondegenerate extension to the C*-algebra
-- statement:
--   A unitary representation $(\pi,\rho^\pi,\mathcal H)$ of a finite-dimensional Lie supergroup determines a unique nondegenerate *-representation $\widehat\pi$ of its $C^*$-algebra $\mathcal A(G,\mathfrak g)$ satisfying
--
--   $$
--   \widehat\pi(D\otimes f)=\rho^\pi(D)\pi(f)
--   \quad(D\in U(\mathfrak g_{\mathbb C}),\ f\in\mathcal D(G_\varepsilon)).
--   $$
--
--   This is the forward object assignment used in Theorem 6.4. Nondegeneracy is the density of the linear span of $\widehat\pi(\mathcal A)\mathcal H$.
--
--   **Formalization Note** Agreement is tested on word generators in the represented algebraic image; finite linear combinations then give the displayed formula. Uniqueness is part of the theorem.
-- source:
--   Neeb–Salmasian, C*-algebras and direct integral decomposition for Lie supergroups, arXiv:1506.01558v1, p. 11, Proposition 6.1

import Mathlib
import Definitions.Def_LieSuperCStar_Correspondence_Setting

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

namespace LieSuperCStar.Correspondence

/-- Proposition 6.1, p. 11: the represented crossed product extends uniquely and
    nondegenerately to its C*-completion. -/
theorem proposition_6_1
    {E G F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
    [Group G] [LieGroup 𝓘(ℝ, E) ∞ G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hc : HCPair E G F) (μ : Measure G) [μ.IsHaarMeasure]
    (π : UnitaryRep hc H) :
    ∃! Ψ : CStarAlg hc μ →⋆ₙₐ[ℂ] (H →L[ℂ] H),
      IsNondegenerate Ψ ∧ Corresponds π Ψ := by sorry

end LieSuperCStar.Correspondence
