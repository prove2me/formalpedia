-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_precision_from_stream_bound_explicit_aux
-- name    : OAI.SubsphereRegression.precision_from_stream_bound_explicit_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:40:10.528066+00:00
-- url     : https://prove2.me/theorems/e45cbbce-fe9e-4595-b06f-da007b38af07
-- title:
--   From the streaming success inequality to $T\ge c\,d\log(1/\varepsilon)$
-- statement:
--   Let $d,M,T,a,q$ be natural numbers and $\varepsilon,A$ real numbers such that
--
--   $$d\ge32,\quad d\le4T,\quad q>0,\quad d\le8q,\quad d\le4a,\quad M\le A\,d^2,\quad A>0,\quad 0<\varepsilon\le1,$$
--
--   and suppose that
--
--   $$
--   \frac23\;\le\;(T+1)\,\bigl(3\cdot4^{d}\,\varepsilon^{a}\bigr)\,\Bigl(32768^{d}\,(2^{M})^{1/q}\Bigr)^{\lfloor T/q\rfloor+1}.
--   $$
--
--   Then
--
--   $$
--   \frac{1}{4\,(256+128A)}\;d\,\log\frac1\varepsilon\;\le\;T,
--   $$
--
--   where $\log$ is the natural logarithm.
--
--   This is the elementary calculus step of the memory–sample lower bound. The hypothesis is the conclusion of the streaming success bound for a learner with $M\le Ad^2$ bits of memory and success probability $2/3$, with parameters $a$ and $q$ of order $d$; the lemma turns it into a lower bound on the number of samples that is linear in $d\log(1/\varepsilon)$, with an explicit constant depending only on $A$.
--
--   **Formalization Note** $\lfloor T/q\rfloor$ is natural-number division `T/q`, $(2^M)^{1/q}$ is a real power (`Real.rpow`), $\varepsilon^a$ and the other powers are natural powers, and $\log$ is `Real.log`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Estimates/Numerics.lean#L13-L96

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

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u

theorem OAI.SubsphereRegression.precision_from_stream_bound_explicit_aux {d M T a q : ℕ} {ε A : ℝ}
    (hd : 32 ≤ d) (hT : d ≤ 4*T) (hq : 0 < q) (hdq : d ≤ 8*q)
    (ha : d ≤ 4*a) (hM : (M : ℝ) ≤ A * (d : ℝ)^2) (hA : 0 < A)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbound : (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1)) :
    (1 / (4*(256+128*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by sorry
