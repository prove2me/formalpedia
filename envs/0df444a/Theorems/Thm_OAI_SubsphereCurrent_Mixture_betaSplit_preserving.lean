-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Mixture_betaSplit_preserving
-- name    : OAI.SubsphereCurrent.Mixture.betaSplit_preserving
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:13:46.213957+00:00
-- url     : https://prove2.me/theorems/e00985fe-96bf-4173-a4d9-a574548d9846
-- title:
--   Beta–gamma algebra: $(QR,(1-Q)R)$ has independent $\mathrm{Gamma}(a)$ and $\mathrm{Gamma}(b)$ coordinates
-- statement:
--   For real parameters $\alpha,\beta$ let $\mathrm{Beta}(\alpha,\beta)$ be the measure on $\mathbb{R}$ with density
--   $$
--   \frac{q^{\alpha-1}(1-q)^{\beta-1}}{B(\alpha,\beta)}\,\mathbf 1_{(0,1)}(q),\qquad B(\alpha,\beta)=\frac{\Gamma(\alpha)\Gamma(\beta)}{\Gamma(\alpha+\beta)},
--   $$
--   and for real $c$ let $\mathrm{Gamma}(c,1)$ be the measure on $\mathbb{R}$ with density $x^{c-1}e^{-x}/\Gamma(c)$ for $x\ge 0$ and $0$ for $x<0$ (shape $c$, rate $1$), both with respect to Lebesgue measure.
--
--   Let $a>0$ and $b>0$, and let $\Phi:\mathbb{R}^2\to\mathbb{R}^2$ be $\Phi(q,r)=(qr,(1-q)r)$. Then $\Phi$ is measure preserving from $\mathrm{Beta}(a,b)\otimes\mathrm{Gamma}(a+b,1)$ to $\mathrm{Gamma}(a,1)\otimes\mathrm{Gamma}(b,1)$:
--   $$
--   \Phi_{*}\bigl(\mathrm{Beta}(a,b)\otimes\mathrm{Gamma}(a+b,1)\bigr)=\mathrm{Gamma}(a,1)\otimes\mathrm{Gamma}(b,1).
--   $$
--
--   Equivalently, if $Q\sim\mathrm{Beta}(a,b)$ and $R\sim\mathrm{Gamma}(a+b,1)$ are independent, then $QR$ and $(1-Q)R$ are independent with laws $\mathrm{Gamma}(a,1)$ and $\mathrm{Gamma}(b,1)$. This classical beta–gamma identity is the basic input for the exact scalar laws used in the comparison of spherical measures: inverting it shows that $G_1/(G_1+G_2)$ is $\mathrm{Beta}(a,b)$-distributed for independent $G_1\sim\mathrm{Gamma}(a,1)$, $G_2\sim\mathrm{Gamma}(b,1)$, which in turn identifies squared projection lengths of uniform random unit vectors and products of independent beta variables.
--
--   **Formalization Note** The measures are Mathlib's `betaMeasure a b` and `gammaMeasure c 1`, defined as Lebesgue measure with the densities above; $\Phi$ is `betaSplit`. `MeasurePreserving` bundles measurability of $\Phi$ with the equality of image measures.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/BetaTheory.lean#L445-L459

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem OAI.SubsphereCurrent.Mixture.betaSplit_preserving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasurePreserving betaSplit ((betaMeasure a b).prod (gammaMeasure (a+b) 1))
      ((gammaMeasure a 1).prod (gammaMeasure b 1)) := by sorry
