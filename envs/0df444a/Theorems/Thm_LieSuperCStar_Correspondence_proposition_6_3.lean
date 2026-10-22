-- Prove2me | Theorems.Thm_LieSuperCStar_Correspondence_proposition_6_3
-- name    : LieSuperCStar.Correspondence.proposition_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:57.892181+00:00
-- url     : https://prove2.me/theorems/81ebf362-7d72-4541-ad21-7db5618c9f86
-- title:
--   Proposition 6.3, p. 12 — reconstructed data form a unitary Lie supergroup representation
-- statement:
--   Let $\Psi$ be a nondegenerate *-representation of $\mathcal A(G,\mathfrak g)$. The multiplier actions of $G$ and the parity element $\varepsilon$, together with the algebraic multiplier action of $x\in\mathfrak g$ on the smooth core $\mathcal H^\circ$, determine a triple $(\pi,\rho^\pi,\mathcal H)$ that satisfies all the axioms of a unitary representation of $(G,\mathfrak g)$.
--
--   On a represented generator, the defining infinitesimal equation is
--
--   $$
--   \rho^\pi(x)\,\Psi(D\otimes f)w=\Psi(xD\otimes f)w.
--   $$
--
--   This supplies the reverse object assignment in Theorem 6.4. The representation type carries the grading, superbracket, symmetry, derived even action, and covariance conditions.
--
--   **Formalization Note** The group and parity multiplier equations are stated with witnesses inside the non-unital algebra, and the infinitesimal equation is stated on smooth vectors themselves.
-- source:
--   Neeb–Salmasian, C*-algebras and direct integral decomposition for Lie supergroups, arXiv:1506.01558v1, p. 12, Proposition 6.3 and equations (19), (21)

import Mathlib
import Definitions.Def_LieSuperCStar_Correspondence_Setting

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

namespace LieSuperCStar.Correspondence

/-- Proposition 6.3, p. 12: the multiplier construction yields a unitary
    representation of the Lie supergroup. -/
theorem proposition_6_3
    {E G F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
    [Group G] [LieGroup 𝓘(ℝ, E) ∞ G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hc : HCPair E G F) (μ : Measure G) [μ.IsHaarMeasure]
    (Ψ : CStarAlg hc μ →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hΨ : IsNondegenerate Ψ) :
    ∃ π : UnitaryRep hc H,
      IsMultExt Ψ π.π ∧
      (∀ a : CStarAlg hc μ, ∃ b : CStarAlg hc μ,
        (b : Big hc) = uEps hc * (a : Big hc) ∧
          ∀ v : H, π.P (Ψ a v) = Ψ b v) ∧
      ∀ u xs f (a b : CStarAlg hc μ),
        IsGen hc μ (a : Big hc) xs f →
        IsGen hc μ (b : Big hc) (u :: xs) f →
        ∀ w : H, ∀ v : smoothVectors (E := E) π.π,
          (v : H) = Ψ a w →
            (((π.ρ u v : smoothVectors (E := E) π.π) : H)) = Ψ b w := by sorry

end LieSuperCStar.Correspondence
