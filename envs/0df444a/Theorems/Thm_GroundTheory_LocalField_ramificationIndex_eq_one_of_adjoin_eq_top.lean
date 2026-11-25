-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ramificationIndex_eq_one_of_adjoin_eq_top
-- name    : GroundTheory.LocalField.ramificationIndex_eq_one_of_adjoin_eq_top
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:31.631619+00:00
-- url     : https://prove2.me/theorems/116d4ab8-5dd6-4269-baa5-2cb8ab660950
-- title:
--   Local Field: ramification Index eq one of adjoin eq top
-- statement:
--   The Local Field construction uses the ramification Index eq one of adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean#L95-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean#L95-L105

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
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
open ValuativeRel Polynomial IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {m : ℕ} {ζ : L}

theorem GroundTheory.LocalField.ramificationIndex_eq_one_of_adjoin_eq_top (hζ : IsPrimitiveRoot ζ m) (hm : (m : 𝓀[K]) ≠ 0)
    (htop : K⟮ζ⟯ = ⊤) : ramificationIndex K L = 1 := by sorry
