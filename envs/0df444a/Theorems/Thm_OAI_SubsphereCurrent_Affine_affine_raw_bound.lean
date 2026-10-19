-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Affine_affine_raw_bound
-- name    : OAI.SubsphereCurrent.Affine.affine_raw_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:06:16.080759+00:00
-- url     : https://prove2.me/theorems/873e6b46-a745-4c30-8a36-a3aa49eae3da
-- title:
--   Numerical bound converting the stream estimate into $(16\cdot1000^{32\ell}\eta)^{2\lfloor d/32\rfloor}$
-- statement:
--   Let $d,n,\ell,J$ be natural numbers and $\eta$ a real number, and set
--   $$q=\Big\lfloor\frac{n-1}{4}\Big\rfloor,\qquad b=\Big\lfloor\frac{\ell\,\lfloor d/16\rfloor}{q}\Big\rfloor+1,\qquad c_\ell=16\cdot1000^{32\ell}.$$
--   Assume that $d\ge128$, $\lfloor(d+1)/2\rfloor+2\ell\le n$, $\ell\ge1$, $J\ge1$, $\ln J\le\lfloor d/8\rfloor\,d\,\ln2$, $\eta>0$ and $c_\ell\,\eta\le1$.
--
--   **Theorem.** Then
--
--   $$
--   \big(3\cdot4^{n}\,\eta^{2q}\big)\Big(32768^{n}\,J^{1/q}\Big)^{b}\;\le\;\big(c_\ell\,\eta\big)^{2\lfloor d/32\rfloor}.
--   $$
--
--   The left side is the general finite-memory stream bound in dimension $n$, with block length $q$, exponent $2q$ and $\ell\lfloor d/16\rfloor$ observations, for a stream with $J$ states; the condition on $\ln J$ says $J\le2^{d\lfloor d/8\rfloor}$, the memory budget of the affine estimate. The lemma converts that bound into the clean form $(16\cdot1000^{32\ell}\eta)^{2\lfloor d/32\rfloor}$ used in the affine estimate, in which the constant grows geometrically with the number $\ell$ of observation blocks while the exponent stays fixed.
--
--   **Formalization Note** All divisions written with integer parts are truncated natural divisions in Lean, $n-1$ is natural subtraction, $J^{1/q}$ is a real power with exponent `1/(((n-1)/4 : ℕ) : ℝ)`, and $\ln$ is `Real.log`; $c_\ell$ appears as `16*((1000 : ℝ)^32)^ell`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Estimates/AffinePrecision.lean#L50-L124

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

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Affine
open scoped ENNReal NNReal

theorem OAI.SubsphereCurrent.Affine.affine_raw_bound {d n ell J : ℕ} {η : ℝ}
    (hd : 128 ≤ d) (hn : (d+1)/2 + 2*ell ≤ n) (hell : 1 ≤ ell)
    (hJ : 1 ≤ J)
    (hbudget : Real.log (J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2)
    (hη : 0 < η) (hsmall : 16*((1000 : ℝ)^32)^ell*η ≤ 1) :
    ((3 : ℝ)*4^n * η^(2*((n-1)/4))) *
      ((32768 : ℝ)^n * (J : ℝ)^(1/(((n-1)/4 : ℕ) : ℝ)))^
        (ell*(d/16)/((n-1)/4)+1) ≤
      (16*((1000 : ℝ)^32)^ell*η)^(2*(d/32)) := by sorry
