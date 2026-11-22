-- Prove2me | Theorems.Thm_NoHair_static_electrovac_areal_reduction
-- name    : NoHair.static_electrovac_areal_reduction
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T20:55:54.408292+00:00
-- url     : https://prove2.me/theorems/f80d033c-ea50-4464-a271-233e2abe1298
-- title:
--   Global areal coordinates and radial field equations for a static electrovac exterior
-- statement:
--   Take a smooth stationary Einstein–Maxwell black hole with the asymptotically flat end, time orientation, globally hyperbolic exterior $D$, nonempty black-hole region and connected future horizon of the mission. Assume its stationary generator is hypersurface-orthogonal on $D$. The requested geometric reduction is a global areal coordinate map from $r>R$ onto $D$, for some $R>0$, with mass function $\mu$ and radial electric and magnetic amplitudes $u,v$.
--
--   In ingoing Kerr–Schild coordinates let $k=dt+dr$, let $\eta$ be the flat metric, and let $F_1$ be the purely electric unit Coulomb two-form. The pullbacks are required to satisfy
--   $$
--   G=\eta+\frac{2\mu(r)}{r}k\otimes k,\qquad
--   F=r^2u(r)F_1+r^2v(r)\star_G F_1 .
--   $$
--   The mass extends continuously to $R$, with $2\mu(R)=R$ and $2\mu(r)<r$ outside. The remaining differential equations are
--   $$
--   u'=-2u/r,\qquad v'=-2v/r,\qquad 2\mu'=r^2(u^2+v^2).
--   $$
--
--   This is the global spherical-symmetry and coordinate-existence part of the mission's static electrovac classification. Israel's equipotential-surface hypotheses, and the hypersurface and boundary hypotheses of Chruściel–Tod Theorem 1.1, require justification in an application to the mission's assumptions.
-- source:
--   Geometric subproblem of the Prove2Me Israel (1968) milestone, https://prove2.me/theorems/ae80f2c5-e7b6-4f5e-ab99-ed248fa30fca. W. Israel, Event horizons in static electrovac space-times, Commun. Math. Phys. 8 (1968), pp. 245–260, https://doi.org/10.1007/BF01645859. See also P. T. Chruściel and P. Tod, Theorem 1.1(i), p. 2, https://arxiv.org/pdf/gr-qc/0512043, for classification under explicit hypersurface hypotheses. K. A. Bronnikov, Dyonic configurations in nonlinear electrodynamics coupled to general relativity, arXiv:1708.08125, p. 1, Eqs. (2)–(5) and p. 4, Eq. (10), Maxwell specialization, https://arxiv.org/pdf/1708.08125. The horizon is a zero of the metric coefficient in Eq. (10).

import Definitions.Def_NoHair_spacetime

open scoped ContDiff Manifold
open Set NoHair

theorem NoHair.static_electrovac_areal_reduction {M : Type*}
    [TopologicalSpace M] [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M]
    (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ (R : ℝ) (μ u v : ℝ → ℝ) (ψ : E4 → M),
      0 < R ∧ ContinuousOn μ (Ici R) ∧ 2 * μ R = R ∧
      (∀ r, R < r → 2 * μ r < r) ∧
      (∀ r, R < r → HasDerivAt u (-2 * u r / r) r) ∧
      (∀ r, R < r → HasDerivAt v (-2 * v r / r) r) ∧
      (∀ r, R < r → HasDerivAt μ (r ^ 2 * (u r ^ 2 + v r ^ 2) / 2) r) ∧
      IsDiffeoOnto ψ {y | R < ksRadius 0 y} (domainOfOuterCommunications g T E.region) ∧
      ∀ y, R < ksRadius 0 y →
        let r := ksRadius 0 y
        let G := kerrNewmanMetric (μ r) 0 0 y
        pullbackCoeffs g ψ y = G ∧
          pullbackCoeffs F ψ y = (r ^ 2 * u r) • kerrNewmanField 0 1 y +
            (r ^ 2 * v r) • hodgeDual G (kerrNewmanField 0 1 y) := by sorry
