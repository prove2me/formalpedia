-- Prove2me | Theorems.Thm_GlobalTheory_LinSchur_addChar_ne_zero
-- name    : GlobalTheory.LinSchur.addChar_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:06.944814+00:00
-- url     : https://prove2.me/theorems/c7cb1182-1a3e-468c-b967-6a9c3acea841
-- title:
--   Lin Schur: add Char ne zero
-- statement:
--   The Lin Schur construction uses the add Char ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh.lean#L51-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenSubgroupPeriodicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetEqSumAddCosetIndicatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LinSchur

theorem GlobalTheory.LinSchur.addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by sorry
