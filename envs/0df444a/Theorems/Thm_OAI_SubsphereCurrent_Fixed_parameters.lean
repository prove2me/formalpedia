-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Fixed_parameters
-- name    : OAI.SubsphereCurrent.Fixed.parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:06:56.177043+00:00
-- url     : https://prove2.me/theorems/fb15b566-8065-4645-97fc-77c590c5bcff
-- title:
--   Parameter inequalities for the block length $q=\lfloor(m-1)/4\rfloor$
-- statement:
--   Let $d,j,m$ be natural numbers with $d\ge64$ and $d/2+2j\le m$ (the second inequality between real numbers), and put $q=\lfloor(m-1)/4\rfloor$.
--
--   **Theorem.** The following five inequalities hold:
--
--   1. $q\ge2$;
--   2. $d\le16q$;
--   3. $\lfloor d/32\rfloor\le q$;
--   4. $d/32\le2q$, as real numbers;
--   5. the number of blocks of length $q$ for $j\lfloor d/32\rfloor$ observations is at most $j+1$:
--
--   $$
--   \Big\lfloor\frac{j\,\lfloor d/32\rfloor}{q}\Big\rfloor+1\;\le\;j+1 .
--   $$
--
--   These are the parameter checks for applying the general finite-memory stream bound in dimension $m$, with block length $q$, to streams with $j\lfloor d/32\rfloor$ observations: $q\ge2$ is required by that bound, $d\le16q$ keeps the memory factor $(2^{d^2})^{1/q}$ at most $2^{16d}$, $d/32\le2q$ lets the exponent $2q$ dominate the target exponent $d/32$, and the last inequality bounds the number of blocks by $j+1$.
--
--   **Formalization Note** The statement is a `let q := (m-1)/4` followed by a conjunction of the five claims; all divisions are truncated natural divisions and $m-1$ is natural subtraction, while claim 4 is stated in $\mathbb R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Estimates/FixedPrecision.lean#L19-L36

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

theorem OAI.SubsphereCurrent.Fixed.parameters {d j m : ℕ} (hd : 64 ≤ d) (hm : (d : ℝ)/2 + 2*j ≤ m) :
    let q := (m-1)/4
    2 ≤ q ∧ d ≤ 16*q ∧ d/32 ≤ q ∧ (d : ℝ)/32 ≤ 2*q ∧
      j*(d/32)/q+1 ≤ j+1 := by sorry
