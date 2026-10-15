-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_precision_from_stream_bound
-- name    : OAI.NoiselessRegression.precision_from_stream_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T09:51:14.555308+00:00
-- url     : https://prove2.me/theorems/a283c952-5252-4428-87ad-19d5a55bcdf6
-- title:
--   From the streaming success inequality to the sample lower bound $T\ge c\,d\log(1/\varepsilon)$
-- statement:
--   Let $d,M,T,a,q$ be natural numbers and $\varepsilon,A$ real numbers such that $d\ge32$, $d\le4T$, $q\ge1$, $d\le8q$, $d\le4a$, $M\le A\,d^{2}$, $A>0$ and $0<\varepsilon\le1$. Suppose that
--
--   $$
--   \frac23\le(T+1)\bigl(3\cdot4^{d}\,\varepsilon^{a}\bigr)\bigl(32768^{d}\,(2^{M})^{1/q}\bigr)^{\lfloor T/q\rfloor+1}.
--   $$
--
--   Then, with $\log$ the natural logarithm,
--
--   $$
--   \frac{1}{4(400000+100A)}\;d\,\log\frac1\varepsilon\le T.
--   $$
--
--   This is the purely arithmetic step that converts the success inequality for learners with $2^M$ memory states into a sample lower bound: when $q$ and $a$ are proportional to $d$ and the memory satisfies $M\le A\,d^{2}$, any sample size $T\ge d/4$ satisfying the inequality must be at least $c_A\,d\log(1/\varepsilon)$, with the explicit constant $c_A=1/(4(400000+100A))$.
--
--   **Formalization Note** $\lfloor T/q\rfloor$ is the natural-number division `T/q`, $(2^M)^{1/q}$ is the real power `((2:ℝ)^M)^(1/(q:ℝ))`, and the logarithm is `Real.log`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Precision.lean#L47-L125

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere
import Definitions.Def_OAI_Probability_GaussianRegression_Stream
import Definitions.Def_OAI_Probability_GaussianRegression_Caps
import Definitions.Def_OAI_Probability_GaussianRegression_Execution
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u

theorem OAI.NoiselessRegression.precision_from_stream_bound {d M T a q : ℕ} {ε A : ℝ}
    (hd : 32 ≤ d) (hT : d ≤ 4*T) (hq : 0 < q) (hdq : d ≤ 8*q)
    (ha : d ≤ 4*a) (hM : (M : ℝ) ≤ A * (d : ℝ)^2) (hA : 0 < A)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbound : (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1)) :
    (1 / (4*(400000+100*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by sorry
