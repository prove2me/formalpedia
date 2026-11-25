-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_eq_adjoin
-- name    : GroundTheory.LocalField.IsUnramifiedSubextension.eq_adjoin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:13.542257+00:00
-- url     : https://prove2.me/theorems/74405b95-c29b-4ea5-a4cc-1388e992235d
-- title:
--   Is Unramified Subextension: eq adjoin
-- statement:
--   The Is Unramified Subextension construction uses the eq adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L123-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L123-L143

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
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
open ValuativeRel IntermediateField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]

theorem GroundTheory.LocalField.IsUnramifiedSubextension.eq_adjoin {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) {n : ℕ} (hEn : Module.finrank K E = n) (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : E = K⟮ζ⟯ := by sorry
