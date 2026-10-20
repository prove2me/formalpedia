-- Prove2me | Theorems.Thm_OAI_SingleFold_Binary_choose_odd_iff
-- name    : OAI.SingleFold.Binary.choose_odd_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:23:58.983195+00:00
-- url     : https://prove2.me/theorems/98cd681b-9957-4173-acc0-19f47de1187a
-- title:
--   Lucas' theorem modulo 2
-- statement:
--   Write $x\preceq y$ if every binary digit of $x$ is at most the corresponding binary digit of $y$. For all $x,y\in\mathbb{N}$,
--   $$
--   \binom yx\equiv1\pmod2\iff x\preceq y .
--   $$
--
--   Binary digit domination becomes the parity of a binomial coefficient. That parity can then be read off arithmetically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Binary.lean#L32-L45

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

theorem OAI.SingleFold.Binary.choose_odd_iff (x y : ℕ) : y.choose x % 2=1 ↔ Bits x y := by sorry
