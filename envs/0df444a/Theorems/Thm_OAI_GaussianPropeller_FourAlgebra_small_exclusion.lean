-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_FourAlgebra_small_exclusion
-- name    : OAI.GaussianPropeller.FourAlgebra.small_exclusion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:21:51.39737+00:00
-- url     : https://prove2.me/theorems/5bb6ac2d-c593-472f-b5eb-49172b90ef62
-- title:
--   Algebraic exclusion of a short centroid
-- statement:
--   Let $t\in[0,0.156]$, let $a,b,c\ge0$ with $a+b+c=1$, and let $H,V,D$ be reals with $H=1-t^2-(a^2+b^2+c^2)t^2$, $\frac35V\le0.250075-0.415\,t+0.324\,t^2$ and $4D=H^2-2V$. Assume the pair bounds
--   $$
--   D\le\Bigl(\frac3\pi\Bigr)^2t^2(1+x)^2(1+y)^2
--   $$
--   for each pair $\{x,y\}$ among $a,b,c$. Then these conditions are contradictory.
--
--   In the four-cell argument, $t$ is the shortest normalized centroid length and $a,b,c$ the residual coefficients of the other three centroids along it. Their residuals are three plane vectors summing to zero, with total squared length $H$, sum of fourth powers of lengths $V$, and common pair Gram determinant $D$; $4D=H^2-2V$ is Heron's formula. So in a four-cell configuration the shortest normalized centroid is longer than $0.156$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/FourAlgebra.lean#L131-L150

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry
import Definitions.Def_OAI_Probability_GaussianPropeller_QuarticCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapCertificates

open OAI OAI.GaussianPropeller
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open scoped RealInnerProductSpace

theorem OAI.GaussianPropeller.FourAlgebra.small_exclusion {t a b c H V D:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ))
    (ha:0≤a) (hb:0≤b) (hc:0≤c) (hs:a+b+c=1)
    (hH:H=1-t^2-(a^2+b^2+c^2)*t^2)
    (hV:(3/5:ℝ)*V≤(10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2)
    (hD:4*D=H^2-2*V)
    (hab:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+b)^2)
    (hac:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+c)^2)
    (hbc:D≤(3/Real.pi)^2*t^2*(1+b)^2*(1+c)^2) : False := by sorry
