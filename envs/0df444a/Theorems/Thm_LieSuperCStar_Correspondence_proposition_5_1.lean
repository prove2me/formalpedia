-- Prove2me | Theorems.Thm_LieSuperCStar_Correspondence_proposition_5_1
-- name    : LieSuperCStar.Correspondence.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:53.468992+00:00
-- url     : https://prove2.me/theorems/c54c9295-0486-4361-a954-e8f7f2869400
-- title:
--   Proposition 5.1, p. 10 — smooth left multiplier orbits
-- statement:
--   Let $\mathcal A^\circ$ be the image of the algebraic crossed product in $\mathcal A(G,\mathfrak g)$. Left multiplication by the multiplier associated to $g\in G$ defines $\eta_G(g)$. For every $a\in\mathcal A^\circ$, the orbit map
--
--   $$
--   G\longrightarrow\mathcal A(G,\mathfrak g),\qquad g\longmapsto\eta_G(g)a
--   $$
--
--   is smooth. This gives the reconstructed group representation smooth vectors in the represented algebraic core.
--
--   **Formalization Note** The statement gives a map into the non-unital closed star subalgebra whose underlying universal operator family is $u_G(g)a$; it asserts smoothness in that subalgebra's normed-space topology.
-- source:
--   Neeb–Salmasian, C*-algebras and direct integral decomposition for Lie supergroups, arXiv:1506.01558v1, p. 10, Proposition 5.1

import Mathlib
import Definitions.Def_LieSuperCStar_Correspondence_Setting

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

namespace LieSuperCStar.Correspondence

/-- Proposition 5.1, p. 10: the left multiplier orbit of an algebraic element is smooth. -/
theorem proposition_5_1
    {E G F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
    [Group G] [LieGroup 𝓘(ℝ, E) ∞ G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hc : HCPair E G F) (μ : Measure G) [μ.IsHaarMeasure]
    (a : Big hc) (ha : a ∈ A0 hc μ) :
    ∃ η : G → CStarAlg hc μ,
      (∀ g : G, (η g : Big hc) = uG hc g * a) ∧
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, CStarAlg hc μ) ∞ η := by sorry

end LieSuperCStar.Correspondence
