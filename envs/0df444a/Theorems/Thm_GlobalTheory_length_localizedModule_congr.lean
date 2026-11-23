-- Prove2me | Theorems.Thm_GlobalTheory_length_localizedModule_congr
-- name    : GlobalTheory.length_localizedModule_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:55.262948+00:00
-- url     : https://prove2.me/theorems/a92b474d-78f9-45d4-8fd4-fb97dbcddc40
-- title:
--   Global Theory: length localized Module congr
-- statement:
--   The Global Theory construction uses the length localized Module congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L63-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {S : Type*} [CommRing S]

theorem GlobalTheory.length_localizedModule_congr (T : Submonoid S) {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N] (e : M ≃ₗ[S] N) :
    Module.length (Localization T) (LocalizedModule T M) =
      Module.length (Localization T) (LocalizedModule T N) := by sorry
