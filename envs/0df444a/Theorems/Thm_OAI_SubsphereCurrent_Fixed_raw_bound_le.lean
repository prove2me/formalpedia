-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Fixed_raw_bound_le
-- name    : OAI.SubsphereCurrent.Fixed.raw_bound_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:07:33.364843+00:00
-- url     : https://prove2.me/theorems/dd4775c2-7e4b-4d14-8a9a-5348a4451f41
-- title:
--   Simplifying the raw fixed-precision stream bound to $(C^{j+1}\eta)^{d/32}$ with $C=e^{2048}$
-- statement:
--   Let $d,j,m$ be natural numbers and $\eta$ a real number such that $d\ge 64$, $\frac d2+2j\le m\le d$ and $0<\eta\le 1$. Put
--   $$
--   q=\Bigl\lfloor\frac{m-1}{4}\Bigr\rfloor,\qquad b=\Bigl\lfloor\frac{j\,\lfloor d/32\rfloor}{q}\Bigr\rfloor+1,\qquad C=e^{2048},
--   $$
--   where the quotients are rounded down (the hypotheses force $q\ge 2$). Then
--   $$
--   \bigl(3\cdot 4^{m}\,\eta^{2q}\bigr)\cdot\Bigl(32768^{m}\,\bigl(2^{d^{2}}\bigr)^{1/q}\Bigr)^{b}\;\le\;\bigl(C^{\,j+1}\,\eta\bigr)^{d/32},
--   $$
--   where on the right the exponent $d/32$ is the real number $d/32$ (not rounded), and $32768=2^{15}$.
--
--   In the fixed-precision dimension estimate, the average probability that a stream on $\mathbb{R}^m$ with $2^{d^2}$ memory states, run for $j\lfloor d/32\rfloor$ steps, ends within Euclidean distance $\eta$ of the hidden unit vector is first bounded by the left-hand side of this inequality. The lemma is the purely arithmetic step that turns this raw bound into the clean form $(C^{j+1}\eta)^{d/32}$, with a constant $C$ independent of all parameters.
--
--   **Formalization Note** `boundConstant` is `Real.exp 2048`. The expressions `(m-1)/4`, `d/32` and `j*(d/32)/((m-1)/4)` are natural-number divisions (rounded down), the power with exponent $b$ and the powers $4^m$, $\eta^{2q}$, $32768^m$, $2^{d^2}$ are natural-number powers, while $(2^{d^2})^{1/q}$ and the right-hand side use the real power `Real.rpow`. Because $m\ge d/2\ge 32$, the truncated subtraction $m-1$ agrees with the ordinary one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Estimates/FixedPrecision.lean#L38-L99

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

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Fixed
open scoped ENNReal NNReal

theorem OAI.SubsphereCurrent.Fixed.raw_bound_le {d j m : ℕ} {η : ℝ}
    (hd : 64 ≤ d) (hm : (d : ℝ)/2 + 2*j ≤ m) (hmd : m ≤ d)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ((3 : ℝ)*4^m * η^(2*((m-1)/4))) *
      ((32768 : ℝ)^m * ((2 : ℝ)^(d^2))^(1/(((m-1)/4 : ℕ) : ℝ)))^
        (j*(d/32)/((m-1)/4)+1) ≤
      (boundConstant^(j+1)*η)^((d : ℝ)/32) := by sorry
