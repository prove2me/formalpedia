-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_kosBlock_mul
-- name    : GlobalTheory.KeyKa.kosBlock_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:50:52.525146+00:00
-- url     : https://prove2.me/theorems/accef6bb-6380-436e-9298-0a2825f8dcdf
-- title:
--   Key Ka: kos Block mul
-- statement:
--   The Key Ka construction uses the kos Block mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L17-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}

theorem GlobalTheory.KeyKa.kosBlock_mul (C C' : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P P' : Matrix (Fin d) (Fin d) R) :
    (kosBlock C P : Matrix (KIx g d N) (KIx g d N) R) * kosBlock C' P' =
      kosBlock (fun j => C j * C' j) (P * P') := by sorry
