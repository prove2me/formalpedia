-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isEisensteinAt_root_of_finrank_le
-- name    : GroundTheory.LocalField.isEisensteinAt_root_of_finrank_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:52.083972+00:00
-- url     : https://prove2.me/theorems/aaadfb42-86ba-480a-a98a-88e6ad81ec1a
-- title:
--   Local Field: is Eisenstein At root of finrank le
-- statement:
--   The Local Field construction uses the is Eisenstein At root of finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L292-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L292-L324

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
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
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]}

theorem GroundTheory.LocalField.isEisensteinAt_root_of_finrank_le (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    (hn : 0 < f.natDegree) {α : 𝒪[L]} (hα : aeval α f = 0)
    (hdeg : Module.finrank K L ≤ f.natDegree) :
    ramificationIndex K L = f.natDegree ∧ Module.finrank K L = f.natDegree ∧ Irreducible α := by sorry
