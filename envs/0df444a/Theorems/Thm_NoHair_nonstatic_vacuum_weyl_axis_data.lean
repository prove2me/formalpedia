-- Prove2me | Theorems.Thm_NoHair_nonstatic_vacuum_weyl_axis_data
-- name    : NoHair.nonstatic_vacuum_weyl_axis_data
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:22:46.597182+00:00
-- url     : https://prove2.me/theorems/863ceb65-3b49-4158-83c4-188a41416f76
-- title:
--   Global Weyl coordinates and matched boundary data for a nonstatic vacuum black hole
-- statement:
--   Let $D$ be the domain of outer communications under the nonstatic axisymmetric vacuum milestone hypotheses. Construct a horizon half-length $\ell\ge0$ and angular momentum $J$, with $\ell>0$ or $J\ne0$. For a Kerr comparison with $m>0$, $m^2-a^2=\ell^2$ and $ma=J$, construct a diffeomorphism from the model exterior to $D$ and a vacuum Ernst pair $(X,Y)$ reconstructing the pulled-back metric in normalized Weyl charts.
--
--   On each exterior part of the axis $X$ tends to zero and $Y$ tends to $4J$ or $-4J$. On the interior of a positive-length horizon interval $X$ has positive limit. For a comparison Kerr pair with the same normalized axis data, the geometric estimates must give
--   $$
--   \sup_{\rho>0,z\in\mathbb R}\sigma<\infty,\qquad
--   \sigma\longrightarrow0\quad(\rho^2+z^2\to\infty).
--   $$
--   This requires uniform control near the horizon endpoints and the regular axis. When $\ell=0$ the puncture represents a degenerate horizon and its near-horizon behavior must be controlled separately. Deriving the necessary global regularity from the mission hypotheses remains part of this statement.
-- source:
--   P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, §§6.4–6.7, eqs. (6.13)–(6.18), (6.45)–(6.47) and Cor. 6.3, https://arxiv.org/abs/0806.0016. For the degenerate end see Amsel et al., pp. 3–5, eqs. (6)–(16), https://arxiv.org/abs/0906.2367. For the global regularity hypotheses see Chruściel, Costa and Heusler, Def. 2.1 and Thm. 3.2, https://arxiv.org/abs/1205.6112. P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, proof of Corollary 6.3, pp. 51–52, https://arxiv.org/abs/0806.0016. S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, eqs. (90)–(95), https://arxiv.org/abs/gr-qc/0508061.

import Definitions.Def_NoHair_kerrWeylModel

open scoped ContDiff Manifold

namespace NoHair

theorem nonstatic_vacuum_weyl_axis_data {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (ρ : ℝ → M → M) (hρ : IsAxialSymmetry g F φ ρ)
    (hns : ¬ IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ ℓ J : ℝ, 0 ≤ ℓ ∧ (0 < ℓ ∨ J ≠ 0) ∧
      ∀ m a : ℝ, 0 < m → m^2-a^2 = ℓ^2 → m*a = J →
        ∃ (Ψ : E4 → M) (u : Weyl.ErnstPotentials),
          IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) (domainOfOuterCommunications g T E.region) ∧
          u.IsSolution ∧ Weyl.HasAxisData u ℓ J ∧
          (Weyl.HasAxisData (Weyl.kerrErnst m a) ℓ J →
            Weyl.HasComparisonBounds u (Weyl.kerrErnst m a)) ∧
          Weyl.IsWeylRepresentation m a (pullbackCoeffs g Ψ) u := by
  sorry

end NoHair
