-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_kosBlock_det_sub
-- name    : GlobalTheory.KeyKa.kosBlock_det_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:50:35.019216+00:00
-- url     : https://prove2.me/theorems/fcb187d4-3212-4fbd-a233-634ece954b26
-- title:
--   Key Ka: kos Block det sub
-- statement:
--   The Key Ka construction uses the kos Block det sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L61-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L61-L92

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

theorem GlobalTheory.KeyKa.kosBlock_det_sub (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (s : ℕ → Prop) [DecidablePred s] :
    ((kosBlock C P : Matrix (KIx g d N) (KIx g d N) R).submatrix
        (fun p : {p // s (kdeg p)} => p.1) (fun p : {p // s (kdeg p)} => p.1)).det =
      (∏ j ∈ Finset.range (g + 1), if s (j + 1) then (C j).det ^ g.choose j else 1) *
        (if s 0 then P.det else 1) := by sorry
