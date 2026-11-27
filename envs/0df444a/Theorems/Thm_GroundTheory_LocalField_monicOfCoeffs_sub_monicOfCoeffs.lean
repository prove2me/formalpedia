-- Prove2me | Theorems.Thm_GroundTheory_LocalField_monicOfCoeffs_sub_monicOfCoeffs
-- name    : GroundTheory.LocalField.monicOfCoeffs_sub_monicOfCoeffs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:57.781053+00:00
-- url     : https://prove2.me/theorems/902705a2-9a9d-52ed-8e61-c12a458ae9e9
-- title:
--   Local Field: monic Of Coeffs sub monic Of Coeffs
-- statement:
--   The Local Field construction uses the monic Of Coeffs sub monic Of Coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L192-L195

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

theorem GroundTheory.LocalField.monicOfCoeffs_sub_monicOfCoeffs {n : ℕ} (c d : Fin n → R) :
    monicOfCoeffs c - monicOfCoeffs d = ∑ i : Fin n, C (c i - d i) * X ^ (i : ℕ) := by sorry
