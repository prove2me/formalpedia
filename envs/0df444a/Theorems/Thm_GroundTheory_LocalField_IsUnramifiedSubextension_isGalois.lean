-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_isGalois
-- name    : GroundTheory.LocalField.IsUnramifiedSubextension.isGalois
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:12.720523+00:00
-- url     : https://prove2.me/theorems/a7efcbbd-7fef-403e-b317-5fc1fd2e7f53
-- title:
--   Is Unramified Subextension: is Galois
-- statement:
--   The Is Unramified Subextension construction uses the is Galois property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L72-L79

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

theorem GroundTheory.LocalField.IsUnramifiedSubextension.isGalois {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : IsGalois K E := by sorry
