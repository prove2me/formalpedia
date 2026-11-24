-- Prove2me | Theorems.Thm_GlobalTheory_JR_NormalFormL_companion_pow_card
-- name    : GlobalTheory.JR.NormalFormL.companion_pow_card
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:34:05.448501+00:00
-- url     : https://prove2.me/theorems/e7a230c3-8a00-4a60-a50d-10307267c55c
-- title:
--   Normal Form L: companion pow card
-- statement:
--   The Normal Form L construction uses the companion pow card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L53-L56

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}

theorem GlobalTheory.JR.NormalFormL.companion_pow_card (p : Fin r → k) (hr : 0 < r) :
    companion p ^ r *ᵥ ev r k 0 = - p := by sorry
