-- Prove2me | Theorems.Thm_OAI_Cotype_projectionLinearCoefficient_bound_of_power_gap
-- name    : OAI.Cotype.projectionLinearCoefficient_bound_of_power_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:07:27.520392+00:00
-- url     : https://prove2.me/theorems/1b770419-fd2e-4901-bdea-3a116e7b8750
-- title:
--   Power gaps bound the linear coefficient of the coordinate semigroup
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. For commuting bounded projections $P_1,\dots,P_m$ on $X$, products are taken in a fixed order, $P_S=\prod_{i\in S}P_i$, and the coordinate semigroup is $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$. Let $N\ge1$ and $0\le C<2^N$. There is $K\ge0$ with the following property. Let $Y$ be a real Banach space and $P_1,\dots,P_m$ commuting contractive idempotents on $Y$ with the power gap $\|(1-T(r))^Ny\|\le C\|y\|$ for all $r\in[0,1]$. Then for all $y\in Y$,
--   $$
--   \Bigl\|\sum_{i=1}^m(1-P_i)\prod_{j\ne i}P_j\,y\Bigr\|\le K\|y\| .
--   $$
--
--   The constant is uniform in $Y$ and $m$; this is the step from a power gap to K-convexity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/CoefficientPowerGap.lean#L10-L39

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
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour

open OAI OAI.Cotype

theorem OAI.Cotype.projectionLinearCoefficient_bound_of_power_gap
    {N : ℕ} (hN : 0 < N) {C : ℝ} (hC : 0 ≤ C)
    (hC2 : C < (2 : ℝ)^N) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [CompleteSpace Y] (m : ℕ) (P : Fin m → Y →L[ℝ] Y),
        (∀ i, P i * P i = P i) →
        (∀ i j, Commute (P i) (P j)) →
        (∀ i y, ‖P i y‖ ≤ ‖y‖) →
        (∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
          ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖) →
        ∀ y : Y, ‖projectionLinearCoefficient P y‖ ≤ K*‖y‖ := by sorry
