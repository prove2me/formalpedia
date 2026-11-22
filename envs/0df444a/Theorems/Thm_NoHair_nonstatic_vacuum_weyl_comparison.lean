-- Prove2me | Theorems.Thm_NoHair_nonstatic_vacuum_weyl_comparison
-- name    : NoHair.nonstatic_vacuum_weyl_comparison
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T20:53:39.96486+00:00
-- url     : https://prove2.me/theorems/6446fdd0-7ce8-497a-b236-26bd4da61c79
-- title:
--   Weyl comparison data for a nonstatic axisymmetric vacuum exterior
-- statement:
--   Let $D$ be the domain of outer communications of a stationary, asymptotically flat vacuum black hole satisfying the Carter–Robinson milestone hypotheses. Assume the spacetime has the stipulated commuting axial symmetry and the stationary field fails the staticity condition on $D$. The geometric reduction asks for a Kerr comparison exterior $D_K$ with
--
--   $$
--   m>0,\qquad a^2\le m^2,
--   $$
--
--   a smooth diffeomorphism $\Psi:D_K\to D$, and two vacuum Ernst maps on $\rho>0$. The metric $\Psi^*g$ is reconstructed from the first map and the Kerr metric from the second, in common Weyl charts on a dense subset of $D_K$. Both metrics extend continuously across the omitted set. The two maps must have bounded deviation up to the axis and horizon, with deviation tending uniformly to zero at spatial infinity.
--
--   Proving this obligation requires constructing the orbit coordinates, matching the horizon and twist boundary data to Kerr, and justifying the radial quadratures and their normalization. The comparison must also cover a degenerate horizon. The literature uses global regularity hypotheses such as $I^+$-regularity to obtain these properties. Establishing the needed properties from the milestone’s stated assumptions is part of this problem.
-- source:
--   P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, §§6.4–6.7, eqs. (6.13)–(6.18), (6.45)–(6.47) and Cor. 6.3, https://arxiv.org/abs/0806.0016. For the degenerate end see Amsel et al., pp. 3–5, eqs. (6)–(16), https://arxiv.org/abs/0906.2367. For the global regularity hypotheses see Chruściel, Costa and Heusler, Def. 2.1 and Thm. 3.2, https://arxiv.org/abs/1205.6112.

import Definitions.Def_NoHair_weylPapapetrou

open scoped ContDiff Manifold

namespace NoHair

theorem nonstatic_vacuum_weyl_comparison {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (ρ : ℝ → M → M) (hρ : IsAxialSymmetry g F φ ρ)
    (hns : ¬ IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
      ∃ (Ψ : E4 → M) (u v : Weyl.ErnstPotentials),
        IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) (domainOfOuterCommunications g T E.region) ∧
        u.IsSolution ∧ v.IsSolution ∧ Weyl.HasComparisonBounds u v ∧
        Weyl.HaveCommonCharts (kerrNewmanDOC m a 0) (pullbackCoeffs g Ψ)
          (kerrNewmanMetric m a 0) u v := by
  sorry

end NoHair
