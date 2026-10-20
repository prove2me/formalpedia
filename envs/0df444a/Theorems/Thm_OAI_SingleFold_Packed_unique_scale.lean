-- Prove2me | Theorems.Thm_OAI_SingleFold_Packed_unique_scale
-- name    : OAI.SingleFold.Packed.unique_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:32:13.166905+00:00
-- url     : https://prove2.me/theorems/39877ed0-b9cb-4b71-a260-1ff5953c5b3b
-- title:
--   A unique power of two between $2L$ and $4L$
-- statement:
--   For every integer $L>0$ there is exactly one $w\in\mathbb{N}$ with
--   $$
--   2L<2^w\le4L .
--   $$
--
--   The base $B=2^w$ of the counter system is thus determined by the machine size. This keeps the witness unique.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Packed.lean#L198-L214

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

theorem OAI.SingleFold.Packed.unique_scale {L : ℕ} (hL : 0 < L) : ∃! w : ℕ, 2*L < 2^w ∧ 2^w ≤ 4*L := by sorry
