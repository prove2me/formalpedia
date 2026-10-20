-- Prove2me | Theorems.Thm_OAI_SingleFold_Packed_bits_testBit
-- name    : OAI.SingleFold.Packed.bits_testBit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:27:07.585902+00:00
-- url     : https://prove2.me/theorems/6f3994b3-b7c3-42cf-9304-cdacef38c5c9
-- title:
--   Binary digit domination in terms of set bits
-- statement:
--   Write $x\preceq y$ if every binary digit of $x$ is at most the corresponding binary digit of $y$. Then
--   $$
--   x\preceq y\iff\bigl(\forall i:\ \text{bit }i\text{ of }x\text{ is }1\implies\text{bit }i\text{ of }y\text{ is }1\bigr).
--   $$
--
--   Domination is thus inclusion of the sets of binary positions. This form is convenient for combining bit masks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Packed.lean#L12-L24

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
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed

open OAI OAI.SingleFold OAI.SingleFold.Packed

theorem OAI.SingleFold.Packed.bits_testBit (x y : ℕ) : Bits x y ↔ ∀ i, x.testBit i=true → y.testBit i=true := by sorry
