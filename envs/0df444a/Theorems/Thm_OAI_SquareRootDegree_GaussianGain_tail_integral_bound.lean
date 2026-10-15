-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_GaussianGain_tail_integral_bound
-- name    : OAI.SquareRootDegree.GaussianGain.tail_integral_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:52:51.741317+00:00
-- url     : https://prove2.me/theorems/f92c3862-0cc0-4249-9881-6d2742e06355
-- title:
--   Gaussian tail bound for the residual of the hat partition of unity
-- statement:
--   Let $\gamma=\mathcal N(0,1)$ be the standard Gaussian measure on $\mathbb R$. With $\operatorname{clip}(x)=\max(0,\min(1,x))$ and, for $N\in\mathbb N$, $\delta\in\mathbb R$ and $i\in\{0,\dots,2N\}$, the hats $\operatorname{hat}_{N,\delta,i}(t)=\operatorname{clip}(t/\delta+N-i+1)-\operatorname{clip}(t/\delta+N-i)$, define the residual
--   $$\rho_{N,\delta}(t)=1-\sum_{i=0}^{2N}\operatorname{hat}_{N,\delta,i}(t),$$
--   the part of the constant function $1$ not covered by the hats. For $h>0$ let $\tau_{1,h}(x)=\max(0,1-|x-1|/h)$ be the tent of half-width $h$ centred at $1$, and $\beta_h=\int\tau_{1,h}\,d\gamma$ its Gaussian mass.
--
--   Let $N\in\mathbb N$ and $\delta,h,R,c,v\in\mathbb R$ satisfy $\delta>0$, $0<h\le1$, $N\delta=R$, $|c-1|\le h$ and $0\le v\le1$. Then
--
--   $$
--   \int_{\mathbb R}\frac{\rho_{N,\delta}(t)\,\big((1+t-c)^2+v\big)}{\beta_h}\,d\gamma(t)\;\le\;\frac{972}{h}\,e^{-R^2/4}.
--   $$
--
--   The residual vanishes on $[-R,R]$, so only the Gaussian tail $|t|>R$ contributes, and the bound decays like $e^{-R^2/4}$ while losing only a factor $1/h$ from the small normalising mass $\beta_h$. In the computation of the Gaussian gain this controls the contribution of the residual weight attached to the middle grid point, whose leaf test is the tent at $1$; there $c$ is the Gaussian mean of that tent and $v$ the sum of the variances of the other leaf tests.
--
--   **Formalization Note** The residual is `residual N δ t`, $\beta_h$ is `mass (gaussianReal 0 1) (tent 1 h)`, and the integral is a Bochner integral with respect to `gaussianReal 0 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/GaussianGain.lean#L273-L324

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.GaussianGain
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
open SmoothGaussian SmoothSelector

theorem OAI.SquareRootDegree.GaussianGain.tail_integral_bound {N : ℕ} {δ h R c v : ℝ} (hδ : 0 < δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hR : N*δ = R) (hc : |c-1| ≤ h)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ t, residual N δ t * ((1+t-c)^2+v) / mass (gaussianReal 0 1) (tent 1 h) ∂gaussianReal 0 1) ≤
      972/h * Real.exp (-(R^2/4)) := by sorry
