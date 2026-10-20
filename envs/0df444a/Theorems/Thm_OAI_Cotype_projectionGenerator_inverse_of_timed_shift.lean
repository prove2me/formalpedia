-- Prove2me | Theorems.Thm_OAI_Cotype_projectionGenerator_inverse_of_timed_shift
-- name    : OAI.Cotype.projectionGenerator_inverse_of_timed_shift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:03:19.551983+00:00
-- url     : https://prove2.me/theorems/42df6fc3-1265-4878-9772-c3a10db2afc0
-- title:
--   Resolvent bounds for the projection generator from a timed shift
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $Y$ be a real normed space and $P_1,\dots,P_m$ commuting idempotent operators on $Y$, lifted to operators $\tilde P_i$ on the complexified bidual $\mathcal Y=\mathcal L_{\mathbb R}(Y^*,\mathbb C)$. For $\varepsilon\in\{0,1\}^m$ let $\Pi_\varepsilon$ be the lifted pattern product with factor $1-P_i$ where $\varepsilon_i=1$ and $P_i$ where $\varepsilon_i=0$, and $|\varepsilon|$ the number of ones. Let $A=\sum_\varepsilon|\varepsilon|\Pi_\varepsilon$ be the generator and $T_t=\prod_i\bigl(\tilde P_i+e^{-t}(1-\tilde P_i)\bigr)$ for $t\in\mathbb C$. Assume the power gap $\|(1-T(r))^Ny\|\le C\|y\|$ for all $r\in[0,1]$ and $y\in Y$, where $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$. Here the $P_i$ are contractions, the complexified bidual is nontrivial, and $C\ge0$, $\rho>0$ with $C<\rho^N$. Let $z\in\mathbb C$, $t\ge0$ and $D$ satisfy $|1-e^{-zt}|\ge\rho$ and $e^{\mathrm{Re}\,z\,(s-t)}\le D$ for $s\in[0,t]$. Then $z-A$ is invertible and
--   $$
--   \|(z-A)^{-1}\|\le Dt\,\frac{\Phi_N(2/\rho,\,C/\rho^N)}{|1-e^{-zt}|},
--   $$
--   where $\Phi_N(b,q)=\bigl(\sum_{k<N}b^k\bigr)/(1-q)$.
--
--   A single time $t$ at which $e^{-zt}$ stays away from $1$ controls the resolvent at $z$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ProjectionResolvent.lean#L106-L137

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

open OAI OAI.Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem OAI.Cotype.projectionGenerator_inverse_of_timed_shift
    [Nontrivial (ComplexDualSpace Y)]
    {N : ℕ} {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ) (hgap : C < ρ^N)
    {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖)
    (hpower : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
      ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖)
    (z : ℂ) {t D : ℝ} (ht : 0 ≤ t)
    (hshift : ρ ≤ ‖1-Complex.exp (-(z*(t : ℂ)))‖)
    (hD : ∀ s ∈ Set.Icc 0 t, Real.exp (z.re * (s-t)) ≤ D) :
    ∃ W : (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)ˣ,
      (W : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) = z • 1 - projectionGenerator P ∧
      ‖(↑W⁻¹ : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)‖ ≤
        D*t * (powerGapInverseBound N (2/ρ) (C/ρ^N) /
          ‖1-Complex.exp (-(z*(t : ℂ)))‖) := by sorry
