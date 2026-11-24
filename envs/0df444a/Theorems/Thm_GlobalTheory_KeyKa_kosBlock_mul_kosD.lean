-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_kosBlock_mul_kosD
-- name    : GlobalTheory.KeyKa.kosBlock_mul_kosD
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:49:41.724123+00:00
-- url     : https://prove2.me/theorems/a68c1214-9153-4be3-bf78-88ad5d3f65cb
-- title:
--   Key Ka: kos Block mul kos D
-- statement:
--   The Key Ka construction uses the kos Block mul kos D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L124-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L124-L161

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

theorem GlobalTheory.KeyKa.kosBlock_mul_kosD (m m' : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (hm : ∀ i j, j < g → C j * m' i j (j + 1) = m i j (j + 1) * C (j + 1))
    (he : P * ev' 0 = ev 0 * C 0) :
    (kosBlock C P * kosD m' ev' : Matrix (KIx g d N) (KIx g d N) R) = kosD m ev * kosBlock C P := by sorry
