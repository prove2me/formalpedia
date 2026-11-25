-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_stabilizer_fixedField_eq
-- name    : GroundTheory.Global.Artin.stabilizer_fixedField_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:47:56.25285+00:00
-- url     : https://prove2.me/theorems/fa9d2cf1-f5ee-440c-8ce2-a60a8b438832
-- title:
--   Artin: stabilizer fixed Field eq
-- statement:
--   The Artin construction uses the stabilizer fixed Field eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L43-L48

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

theorem GroundTheory.Global.Artin.stabilizer_fixedField_eq (P : Ideal (𝓞 L)) :
    MulAction.stabilizer Gal(L/fixedField H) P =
      (MulAction.stabilizer H P).map (fixedFieldMulEquiv H).toMonoidHom := by sorry
