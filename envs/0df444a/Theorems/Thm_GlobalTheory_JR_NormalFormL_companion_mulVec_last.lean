-- Prove2me | Theorems.Thm_GlobalTheory_JR_NormalFormL_companion_mulVec_last
-- name    : GlobalTheory.JR.NormalFormL.companion_mulVec_last
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:34:49.43484+00:00
-- url     : https://prove2.me/theorems/5ce25f1f-05f5-4888-a4ee-949e3c226b6d
-- title:
--   Normal Form L: companion mul Vec last
-- statement:
--   The Normal Form L construction uses the companion mul Vec last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L41-L45

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

theorem GlobalTheory.JR.NormalFormL.companion_mulVec_last (p : Fin r → k) (i : ℕ) (hi : i + 1 = r) :
    companion p *ᵥ ev r k i = - p := by sorry
