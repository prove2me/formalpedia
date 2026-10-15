-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_SmoothGaussian_beta_lower
-- name    : OAI.SquareRootDegree.SmoothGaussian.beta_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:48:51.416998+00:00
-- url     : https://prove2.me/theorems/90bc7ba5-5c6b-4d87-a544-ec54562c7472
-- title:
--   Lower bound for the Gaussian mass of a triangular bump
-- statement:
--   For $a\in\mathbb R$ and $h>0$ let
--   $$\tau_{a,h}(x)=\max\Big(0,\,1-\frac{|x-a|}{h}\Big)$$
--   be the triangular bump (tent) of height $1$ centred at $a$ and supported on $[a-h,a+h]$, and let $\gamma=\mathcal N(0,1)$ be the standard Gaussian measure on $\mathbb R$, whose density is $\varphi(x)=(2\pi)^{-1/2}e^{-x^2/2}$. Then
--
--   $$
--   \frac h2\cdot\frac{1}{\sqrt{2\pi}}\,e^{-(|a|+h)^2/2}\;\le\;\int_{\mathbb R}\tau_{a,h}(x)\,d\gamma(x).
--   $$
--
--   Thus the Gaussian mass of a tent is at least $h/2$ times the Gaussian density at the point $|a|+h$, the far end of its support. In particular it is strictly positive, which matters because these masses appear as denominators (normalising constants of conditional means and variances) when tents are used as soft interval tests.
--
--   **Formalization Note** The tent is `tent a h`, the Gaussian measure is `gaussianReal 0 1`, and the integral is a Bochner integral.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/SmoothGaussian.lean#L80-L113

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.SmoothGaussian
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

theorem OAI.SquareRootDegree.SmoothGaussian.beta_lower {a h : ℝ} (hh : 0 < h) :
    h/2 * ((Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-((|a|+h)^2)/2)) ≤
      ∫ x, tent a h x ∂gaussianReal 0 1 := by sorry
