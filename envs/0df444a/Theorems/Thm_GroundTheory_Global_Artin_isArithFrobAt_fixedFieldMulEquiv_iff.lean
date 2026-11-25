-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_isArithFrobAt_fixedFieldMulEquiv_iff
-- name    : GroundTheory.Global.Artin.isArithFrobAt_fixedFieldMulEquiv_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:21.677072+00:00
-- url     : https://prove2.me/theorems/13296e33-8018-52d5-ac00-cabf5b52f314
-- title:
--   Artin: is Arith Frob At fixed Field Mul Equiv iff
-- statement:
--   The Artin construction uses the is Arith Frob At fixed Field Mul Equiv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L59-L62

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

theorem GroundTheory.Global.Artin.isArithFrobAt_fixedFieldMulEquiv_iff (h : H) (P : Ideal (𝓞 L)) :
    IsArithFrobAt (𝓞 (fixedField H)) (fixedFieldMulEquiv H h) P ↔
      IsArithFrobAt (𝓞 (fixedField H)) h P := by sorry
