-- Prove2me | Theorems.Thm_NoHair_analytic_nonstatic_exterior_weyl_comparison
-- name    : NoHair.analytic_nonstatic_exterior_weyl_comparison
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T20:59:42.515021+00:00
-- url     : https://prove2.me/theorems/1faeab44-9486-4b74-9c6d-cf8fc35710ae
-- title:
--   Weyl comparison data for a nonstatic analytic vacuum exterior with a non-degenerate horizon
-- statement:
--   Let $D$ be the domain of outer communications of a stationary, asymptotically flat vacuum black hole with the connected-horizon and global-hyperbolicity assumptions of the Hawking–Carter–Robinson milestone. Suppose the spacetime and metric are real analytic, the horizon is non-degenerate, and the stationary Killing field fails to be hypersurface-orthogonal on $D$.
--
--   There are Kerr parameters $m>0$ and $a^2\le m^2$, a diffeomorphism $\Psi$ from the Kerr exterior $D_K$ onto $D$, and two vacuum Ernst maps $u,v$ on $\rho>0$. In common Weyl–Papapetrou charts on a dense subset of $D_K$, the normalized radial quadratures of $u$ give the coefficients of $\Psi^*g$ and those of $v$ give the Kerr coefficients. Both coefficient matrices are continuous on $D_K$. If $X_u,Y_u$ and $X_v,Y_v$ are the axial norms squared and twist potentials, the comparison scalar satisfies
--
--   $$
--   \sigma=\frac{(X_u-X_v)^2+(Y_u-Y_v)^2}{X_u X_v},\qquad \sup_{\rho>0,z\in\mathbb R}\sigma<\infty,\qquad \lim_{\rho^2+z^2\to\infty}\sigma=0
--   $$
--
--   with uniform decay at infinity. This geometric step prepares the independent elliptic uniqueness argument. Its obligations include obtaining exterior axial symmetry by rigidity and staticity, matching the horizon interval and twist normalization, and controlling the ends of that interval. The cited proofs assume $I^+$-regularity. Using them here requires deriving the needed horizon-section and orbit-space properties from the mission’s stated hypotheses, or obtaining the same comparison data by another argument.
-- source:
--   P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, Astérisque 321 (2008), 195–265, Def. 1.1, Thms. 1.3 and 4.14, §§6.2–6.7 (Cor. 6.3 and Eqs. (6.13)–(6.18), (6.45)–(6.47)) and §§7.1–7.2. https://arxiv.org/abs/0806.0016. The statement isolates the pre-uniqueness comparison data for the milestone’s hypotheses.

import Definitions.Def_NoHair_weylPapapetrou

open scoped ContDiff Manifold

namespace NoHair

/-- Exterior Weyl comparison data in the nonstatic branch of analytic vacuum rigidity. -/
theorem analytic_nonstatic_exterior_weyl_comparison {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region))
    (hns : ¬ IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
      ∃ (Ψ : E4 → M) (u v : Weyl.ErnstPotentials),
        IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) (domainOfOuterCommunications g T E.region) ∧
        u.IsSolution ∧ v.IsSolution ∧ Weyl.HasComparisonBounds u v ∧
        Weyl.HaveCommonCharts (kerrNewmanDOC m a 0) (pullbackCoeffs g Ψ)
          (kerrNewmanMetric m a 0) u v := by
  sorry

end NoHair
