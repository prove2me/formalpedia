-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_fixedFieldMulEquiv_apply
-- name    : GroundTheory.Global.Artin.fixedFieldMulEquiv_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:47:10.163792+00:00
-- url     : https://prove2.me/theorems/b00df160-720b-458c-ae20-d9c4692d8259
-- title:
--   Artin: fixed Field Mul Equiv apply
-- statement:
--   The Artin construction uses the fixed Field Mul Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L25-L26

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesInfinite
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
omit [IsGalois K L]

theorem GroundTheory.Global.Artin.fixedFieldMulEquiv_apply (h : H) (y : L) : fixedFieldMulEquiv H h y = (h : Gal(L/K)) y := by sorry

attribute [defeq] GroundTheory.Global.Artin.fixedFieldMulEquiv_apply
