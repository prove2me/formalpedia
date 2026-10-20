-- Prove2me | Theorems.Thm_OAI_Cotype_uniform_projectionResolvent_bound_of_power_gap
-- name    : OAI.Cotype.uniform_projectionResolvent_bound_of_power_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:05:55.480002+00:00
-- url     : https://prove2.me/theorems/33f73542-9d3e-466d-a178-d3754a2d39ee
-- title:
--   Uniform sectorial resolvent bounds from a power gap
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $N\in\mathbb N$ and $0\le C<2^N$. There are $a>0$ and $M\ge0$ with the following property. Let $Y$ be any real normed space and $P_1,\dots,P_m$ commuting contractive idempotents on $Y$ satisfying the power gap $\|(1-T(r))^Ny\|\le C\|y\|$ for $r\in[0,1]$, where $T(r)=\prod_i(P_i+r(1-P_i))$. With $\Pi_\varepsilon$ and $|\varepsilon|$ as for the lifted pattern projections, the resolvent
--   $$
--   R(z)=\sum_{\varepsilon\in\{0,1\}^m}\frac{\Pi_\varepsilon}{z-|\varepsilon|}
--   $$
--   satisfies $\|R(z)\|\le M/|z|$ for every nonzero $z$ with $\mathrm{Re}\,z\le a|\mathrm{Im}\,z|$.
--
--   The constants depend only on $N$ and $C$, not on $Y$ or $m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/SectorResolvent.lean#L58-L97

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent

open OAI OAI.Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem OAI.Cotype.uniform_projectionResolvent_bound_of_power_gap
    {N : ℕ} {C : ℝ} (hC : 0 ≤ C) (hC2 : C < (2 : ℝ)^N) :
    ∃ a M : ℝ, 0 < a ∧ 0 ≤ M ∧
      ∀ (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        (m : ℕ) (P : Fin m → Y →L[ℝ] Y),
        (∀ i, P i * P i = P i) →
        (∀ i j, Commute (P i) (P j)) →
        (∀ i y, ‖P i y‖ ≤ ‖y‖) →
        (∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
          ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖) →
        ∀ z : ℂ, z ≠ 0 → z.re ≤ a*|z.im| →
          ‖projectionResolvent P z‖ ≤ M/‖z‖ := by sorry
