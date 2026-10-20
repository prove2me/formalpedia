-- Prove2me | Theorems.Thm_OAI_SingleFold_Binary_choose_digit
-- name    : OAI.SingleFold.Binary.choose_digit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:24:44.250095+00:00
-- url     : https://prove2.me/theorems/c88d6a32-372c-4814-ac03-51a87f07b193
-- title:
--   Binomial coefficients as digits of $(B+1)^y$
-- statement:
--   Let $x\le y$ and $B>2^y$. Then the base-$B$ digit of $(B+1)^y$ at position $x$ is $\binom yx$:
--   $$
--   \Bigl\lfloor\frac{(B+1)^y}{B^x}\Bigr\rfloor\bmod B=\binom yx .
--   $$
--
--   This is how a binomial coefficient is computed by polynomial operations and one division with remainder.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Binary.lean#L74-L87

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary

open OAI OAI.SingleFold OAI.SingleFold.Binary

theorem OAI.SingleFold.Binary.choose_digit {x y B : ℕ} (hxy : x≤y) (hB : 2^y<B) :
    (B+1)^y/B^x%B=y.choose x := by sorry
