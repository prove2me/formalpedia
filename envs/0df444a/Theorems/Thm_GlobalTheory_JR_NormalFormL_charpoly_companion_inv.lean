-- Prove2me | Theorems.Thm_GlobalTheory_JR_NormalFormL_charpoly_companion_inv
-- name    : GlobalTheory.JR.NormalFormL.charpoly_companion_inv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:33.473323+00:00
-- url     : https://prove2.me/theorems/5e412f5d-2422-445a-9bf4-24af66ea0531
-- title:
--   Normal Form L: charpoly companion inv
-- statement:
--   The Normal Form L construction uses the charpoly companion inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L102-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L102-L113

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

theorem GlobalTheory.JR.NormalFormL.charpoly_companion_inv (Y : Gl r k) : (companion (inv Y).1).charpoly = Y.1.charpoly := by sorry
