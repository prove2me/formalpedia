-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_kosBlock_det
-- name    : GlobalTheory.KeyKa.kosBlock_det
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:50:22.277347+00:00
-- url     : https://prove2.me/theorems/1e943e4c-c552-44b3-ae06-19333b84381f
-- title:
--   Key Ka: kos Block det
-- statement:
--   The Key Ka construction uses the kos Block det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L37-L48

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

theorem GlobalTheory.KeyKa.kosBlock_det (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R) :
    (kosBlock C P : Matrix (KIx g d N) (KIx g d N) R).det =
      (∏ j ∈ Finset.range (g + 1), (C j).det ^ g.choose j) * P.det := by sorry
