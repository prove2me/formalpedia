-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_18
-- name    : OAI.GaussianPropeller.FourCertificates.large_18
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:13:09.058742+00:00
-- url     : https://prove2.me/theorems/e27efc91-3266-4f48-8fb6-20a080f1af45
-- title:
--   Large-centroid certificate row on $[0.445,0.4475]$
-- statement:
--   Let $p(x)$ be the standard normal tail probability, $\lambda$ the inverse Mills ratio, $G=\lambda(\lambda-x)$ and $L(x)=p(x)^2G(x)$ the loss function. Let $Q_{\mathrm{large}}(r)=\frac{13}{20}r^2+\frac9{100}$. If $0.445\le r\le0.4475$, $x\ge0$ and
--   $$
--   \frac9{8\pi}\cdot\frac{r^2}{1+\sqrt{1-\frac43r^2}}\le L(x),
--   $$
--   then $Q_{\mathrm{large}}(r)<p(x)$.
--
--   This is one row of the table giving the lower bound $\frac{13}{20}r^2+\frac9{100}$ on the mass of a cell with a long normalized centroid in a four-cell counterexample.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/LargeCertificates.lean#L397-L415

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

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.FourCertificates
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
open OneCell ProbabilityBounds Mills Taylor

theorem OAI.GaussianPropeller.FourCertificates.large_18 {r x:ℝ} (hr:r∈Icc (89/200:ℝ) (179/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by sorry
