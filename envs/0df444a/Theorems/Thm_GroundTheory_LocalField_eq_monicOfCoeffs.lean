-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_monicOfCoeffs
-- name    : GroundTheory.LocalField.eq_monicOfCoeffs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:01.555838+00:00
-- url     : https://prove2.me/theorems/e8788918-2be5-5834-9193-464ce97201e2
-- title:
--   Local Field: eq monic Of Coeffs
-- statement:
--   The Local Field construction uses the eq monic Of Coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L187-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L187-L190

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

theorem GroundTheory.LocalField.eq_monicOfCoeffs {g : R[X]} (hg : g.Monic) {n : ℕ} (hn : g.natDegree = n) :
    g = monicOfCoeffs (fun i : Fin n ↦ g.coeff i) := by sorry
