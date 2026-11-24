-- Prove2me | Theorems.Thm_GlobalTheory_JR_NormalFormL_mom_sec_inv
-- name    : GlobalTheory.JR.NormalFormL.mom_sec_inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:34:12.105854+00:00
-- url     : https://prove2.me/theorems/d2aaacd5-0c50-4639-8456-509cb748ea50
-- title:
--   Normal Form L: mom sec inv
-- statement:
--   The Normal Form L construction uses the mom sec inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L130-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L130-L141

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

theorem GlobalTheory.JR.NormalFormL.mom_sec_inv (Y : Gl r k) (n : ℕ) : mom (sec (inv Y)) n = mom Y n := by sorry
