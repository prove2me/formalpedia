-- Prove2me | Theorems.Thm_GroundTheory_LocalField_FormalGroup_eq_inv_of_subst_eq_zero
-- name    : GroundTheory.LocalField.FormalGroup.eq_inv_of_subst_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:26.092462+00:00
-- url     : https://prove2.me/theorems/e91e13a6-f625-468e-b68e-f7c14829124a
-- title:
--   Formal Group: eq inv of subst eq zero
-- statement:
--   The Formal Group construction uses the eq inv of subst eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FormalGroups/Inverse.lean#L115-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FormalGroups/Inverse.lean#L115-L124

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FormalGroups_Truncation
import Definitions.Def_GroundTheory_LocalFields_FormalGroups_Inverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open MvPowerSeries
variable {R : Type*} [CommRing R] (F : FormalGroup R)

theorem GroundTheory.LocalField.FormalGroup.eq_inv_of_subst_eq_zero {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (h : subst ![PowerSeries.X, g] F.toPowerSeries = (0 : PowerSeries R)) : g = inv F := by sorry
