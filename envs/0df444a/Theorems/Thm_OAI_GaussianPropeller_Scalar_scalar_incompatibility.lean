-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Scalar_scalar_incompatibility
-- name    : OAI.GaussianPropeller.Scalar.scalar_incompatibility
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:27:49.770027+00:00
-- url     : https://prove2.me/theorems/0e4d1dcd-df0f-4385-850e-8e783bb93607
-- title:
--   No scalar data for five or more cells
-- statement:
--   Let $m\ge5$ and let $r_0\ge\dots\ge r_{m-1}>0$ with $r_i\le\frac23$ and $\sum_ir_i^2=1$, and $P_i$ with $\sum_iP_i=1$. Suppose that for all $i$
--   $$
--   \theta_m\,r_i^2\le P_i,\qquad 0.415\,r_i+0.15\,r_i^2\le P_i,
--   $$
--   with $\theta_5=0.929$ and $\theta_m=0.884$ for $m\ge6$. Suppose also, with $t=r_{m-1}$, that $(r_2^2-t^2)(r_0^2+r_1^2-r_2^2-2t^2)\le8(3/\pi)^2t^2$ and $\frac32(r_2^2-t^2)^2\le10(3/\pi)^2t^2$. Then these conditions are contradictory.
--
--   These are the scalar shadows of a configuration with $m$ cells, so no counterexample with five or more cells exists.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Scalar.lean#L605-L632

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
import Definitions.Def_OAI_Probability_GaussianPropeller_Scalar

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Scalar
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

theorem OAI.GaussianPropeller.Scalar.scalar_incompatibility {m : ℕ} (hm : 5 ≤ m) (r P : ℕ → ℝ)
    (hpos : ∀ i < m, 0 < r i) (hordered : AntitoneOn r (Set.Iio m))
    (hcap : ∀ i < m, r i ≤ 2 / 3)
    (hnorm : ∑ i ∈ Finset.range m, r i ^ 2 = 1)
    (hprob : ∑ i ∈ Finset.range m, P i = 1)
    (hquad : ∀ i < m, (if m = 5 then (0.929 : ℝ) else 0.884) * r i ^ 2 ≤ P i)
    (hlin : ∀ i < m, 0.415 * r i + 0.15 * r i ^ 2 ≤ P i)
    (hdet₁ : (r 2 ^ 2 - r (m - 1) ^ 2) *
      (r 0 ^ 2 + r 1 ^ 2 - r 2 ^ 2 - 2 * r (m - 1) ^ 2) ≤
        8 * (3 / Real.pi) ^ 2 * r (m - 1) ^ 2)
    (hdet₂ : (3 / 2 : ℝ) * (r 2 ^ 2 - r (m - 1) ^ 2) ^ 2 ≤
      10 * (3 / Real.pi) ^ 2 * r (m - 1) ^ 2) : False := by sorry
