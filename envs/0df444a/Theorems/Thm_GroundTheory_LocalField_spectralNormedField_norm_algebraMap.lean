-- Prove2me | Theorems.Thm_GroundTheory_LocalField_spectralNormedField_norm_algebraMap
-- name    : GroundTheory.LocalField.spectralNormedField_norm_algebraMap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:14.3781+00:00
-- url     : https://prove2.me/theorems/d3eec362-2a27-4868-8174-23c66d6e7509
-- title:
--   Local Field: spectral Normed Field norm algebra Map
-- statement:
--   The Local Field construction uses the spectral Normed Field norm algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FiniteExtension.lean#L90-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FiniteExtension.lean#L90-L95

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.spectralNormedField_norm_algebraMap (a : K) :
    letI := normedField K
    letI := spectralNormedField K L
    ‖algebraMap K L a‖ = ‖a‖ := by sorry
