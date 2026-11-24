-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_mul_ofAdd_one_le_of_lt_one
-- name    : GlobalTheory.NormEq.mul_ofAdd_one_le_of_lt_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:35:21.569969+00:00
-- url     : https://prove2.me/theorems/b116d4d6-2352-459b-b565-1fe95fd26a8f
-- title:
--   Norm Eq: mul of Add one le of lt one
-- statement:
--   The Norm Eq construction uses the mul of Add one le of lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormApproximationFirstLevel.lean#L126-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormApproximationFirstLevel.lean#L126-L135

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.NormEq.mul_ofAdd_one_le_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) :
    a * ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by sorry
