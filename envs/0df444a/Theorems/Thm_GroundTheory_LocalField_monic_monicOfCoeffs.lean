-- Prove2me | Theorems.Thm_GroundTheory_LocalField_monic_monicOfCoeffs
-- name    : GroundTheory.LocalField.monic_monicOfCoeffs
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:43.650987+00:00
-- url     : https://prove2.me/theorems/a4ec2878-3338-5200-ab08-6e7b9d598e8e
-- title:
--   Local Field: monic monic Of Coeffs
-- statement:
--   The Local Field construction uses the monic monic Of Coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L179-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L179-L180

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Polynomial IntermediateField ValuativeRel
open GroundTheory GroundTheory.LocalField
variable {R : Type*} [CommRing R]

theorem GroundTheory.LocalField.monic_monicOfCoeffs {n : ℕ} (c : Fin n → R) : (monicOfCoeffs c).Monic := by sorry
