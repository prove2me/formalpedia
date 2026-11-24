-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_kosBlock_mul_inr
-- name    : GlobalTheory.KeyKa.kosBlock_mul_inr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:50:36.777026+00:00
-- url     : https://prove2.me/theorems/73c670c0-f47b-448b-8e06-5f679434fc06
-- title:
--   Key Ka: kos Block mul inr
-- statement:
--   The Key Ka construction uses the kos Block mul inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L103-L107

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

theorem GlobalTheory.KeyKa.kosBlock_mul_inr (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (D : Matrix (KIx g d N) (KIx g d N) R) (a : Fin d) (q : KIx g d N) :
    (kosBlock C P * D : Matrix (KIx g d N) (KIx g d N) R) (.inr a) q = ∑ c, P a c * D (.inr c) q := by sorry
