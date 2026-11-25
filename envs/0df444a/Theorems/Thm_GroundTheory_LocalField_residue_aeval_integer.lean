-- Prove2me | Theorems.Thm_GroundTheory_LocalField_residue_aeval_integer
-- name    : GroundTheory.LocalField.residue_aeval_integer
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:12:05.435048+00:00
-- url     : https://prove2.me/theorems/5cc295b1-f38a-4684-940a-197c4d7b5e4d
-- title:
--   Local Field: residue aeval integer
-- statement:
--   The Local Field construction uses the residue aeval integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Monogenic.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Monogenic.lean#L15-L18

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_Monogenic
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
open ValuativeRel Polynomial IsDiscreteValuationRing IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.residue_aeval_integer (p : 𝒪[K][X]) (x : 𝒪[L]) :
    residue 𝒪[L] (aeval x p) = aeval (residue 𝒪[L] x) (p.map (residue 𝒪[K])) := by sorry
