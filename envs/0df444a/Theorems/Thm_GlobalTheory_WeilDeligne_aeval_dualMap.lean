-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_aeval_dualMap
-- name    : GlobalTheory.WeilDeligne.aeval_dualMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:17.835419+00:00
-- url     : https://prove2.me/theorems/95b65bd2-8402-5a17-941f-549adcd760bf
-- title:
--   Weil Deligne: aeval dual Map
-- statement:
--   The Weil Deligne construction uses the aeval dual Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L63-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem GlobalTheory.WeilDeligne.aeval_dualMap (f : End ℂ V) (p : ℂ[X]) :
    aeval (f.dualMap : End ℂ (Dual ℂ V)) p = (aeval f p : End ℂ V).dualMap := by sorry
