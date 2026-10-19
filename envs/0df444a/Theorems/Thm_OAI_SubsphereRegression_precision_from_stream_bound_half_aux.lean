-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_precision_from_stream_bound_half_aux
-- name    : OAI.SubsphereRegression.precision_from_stream_bound_half_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:05:10.83628+00:00
-- url     : https://prove2.me/theorems/d839fd34-c547-4ff3-8d5a-e640da98f956
-- title:
--   From a half-success streaming bound to the sample lower bound $T\ge c\,d\ln(1/\varepsilon)$
-- statement:
--   Let $d,M,T,a,q$ be natural numbers and $\varepsilon,A$ real numbers such that
--   $$32\le d\le32T,\qquad q>0,\qquad d\le8q,\qquad d\le4a,\qquad M\le A\,d^2,\qquad A>0,\qquad 0<\varepsilon\le1,$$
--   and suppose that
--   $$\frac12\le(T+1)\,\big(3\cdot4^{d}\,\varepsilon^{a}\big)\,\Big(32768^{d}\,\big(2^{M}\big)^{1/q}\Big)^{\lfloor T/q\rfloor+1}.$$
--
--   **Theorem.** Then
--
--   $$
--   \frac{1}{4\,(1024+512A)}\;d\,\ln\frac1\varepsilon\;\le\;T .
--   $$
--
--   Here $\ln$ is the natural logarithm and $\lfloor T/q\rfloor$ is the integer part of $T/q$. The hypothesis has the shape of the finite-memory success bound for a learner with $2^M$ states: a union over the $T+1$ possible stopping times, each contributing at most $3\cdot4^d\varepsilon^a$ times a factor $32768^d\,2^{M/q}$ per block of $q$ samples. The lemma is the purely numerical step that turns the compatibility of success probability $1/2$ with this bound into a sample lower bound of order $d\log(1/\varepsilon)$, with an explicit constant, as long as the memory is at most $A\,d^2$ bits.
--
--   **Formalization Note** In Lean, $(2^M)^{1/q}$ is a real power, the exponent $\lfloor T/q\rfloor+1$ is `T/q+1` with truncated natural division, and $\ln$ is `Real.log`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Estimates/HalfPrecision.lean#L204-L287

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

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u

theorem OAI.SubsphereRegression.precision_from_stream_bound_half_aux {d M T a q : ℕ} {ε A : ℝ}
    (hd : 32 ≤ d) (hT : d ≤ 32*T) (hq : 0 < q) (hdq : d ≤ 8*q)
    (ha : d ≤ 4*a) (hM : (M : ℝ) ≤ A * (d : ℝ)^2) (hA : 0 < A)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbound : (1/2 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1)) :
    (1 / (4*(1024+512*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by sorry
