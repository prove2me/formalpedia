-- Prove2me | Theorems.Thm_NoHair_analytic_nonstatic_exterior_axis_data
-- name    : NoHair.analytic_nonstatic_exterior_axis_data
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:34:37.662584+00:00
-- url     : https://prove2.me/theorems/6f571f1e-26aa-4bbe-afcd-432f79abc1ab
-- title:
--   Rod data and Weyl representation of a nonstatic analytic vacuum exterior
-- statement:
--   Consider the domain of outer communications of the analytic, non-degenerate stationary vacuum milestone, and assume its stationary field is nonstatic on that domain. There exist a half-length $\ell\ge 0$ of the horizon interval and a twist normalization $J$, with $\ell>0$ or $J\ne0$. For parameters $m>0$, $m^2-a^2=\ell^2$, $ma=J$, the physical exterior admits a diffeomorphism from the candidate Kerr exterior and has a vacuum Ernst map $u$ in the common orbit coordinates. Its axial norm tends to zero on the exterior axis, its twist tends to $4J$ and $-4J$ on the two axis components, and its axial norm has positive interior horizon limits. Its normalized Weyl quadratures recover the pulled-back metric in each chart. For the explicit Kerr map with those axis data, the comparison scalar is globally bounded and decays uniformly at spatial infinity.
--
--   The endpoint estimates, coordinate construction and existence of an exterior rotational symmetry are geometric obligations in this statement. The standard proofs use $I^+$-regularity. Applying them here requires obtaining the needed exterior regularity from the stated hypotheses.
-- source:
--   P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, Astérisque 321 (2008), Def. 1.1, Thm. 4.14, Cor. 6.3, §§6.2–6.7 and 7.1–7.2, especially Eqs. (6.13)–(6.18) and (6.45)–(6.47). https://arxiv.org/abs/0806.0016. This is a proposed exterior reduction for the mission hypotheses.

import Definitions.Def_NoHair_kerrWeylModel

open scoped ContDiff Manifold

namespace NoHair

theorem analytic_nonstatic_exterior_axis_data {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region))
    (hns : ¬ IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ ℓ J : ℝ, 0 ≤ ℓ ∧ (0 < ℓ ∨ J ≠ 0) ∧
      ∀ m a : ℝ, 0 < m → m^2 - a^2 = ℓ^2 → m*a = J →
        ∃ (Ψ : E4 → M) (u : Weyl.ErnstPotentials),
          IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) (domainOfOuterCommunications g T E.region) ∧
          u.IsSolution ∧ Weyl.HasAxisData u ℓ J ∧
          (Weyl.HasAxisData (Weyl.kerrErnst m a) ℓ J →
            Weyl.HasComparisonBounds u (Weyl.kerrErnst m a)) ∧
          Weyl.IsWeylRepresentation m a (pullbackCoeffs g Ψ) u := by
  sorry

end NoHair
