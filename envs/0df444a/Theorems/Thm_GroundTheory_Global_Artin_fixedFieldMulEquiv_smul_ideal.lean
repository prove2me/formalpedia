-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_fixedFieldMulEquiv_smul_ideal
-- name    : GroundTheory.Global.Artin.fixedFieldMulEquiv_smul_ideal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:47:31.54423+00:00
-- url     : https://prove2.me/theorems/504ec264-630a-4660-b9b3-f7eebbc43350
-- title:
--   Artin: fixed Field Mul Equiv smul ideal
-- statement:
--   The Artin construction uses the fixed Field Mul Equiv smul ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L34-L39

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

theorem GroundTheory.Global.Artin.fixedFieldMulEquiv_smul_ideal (h : H) (P : Ideal (𝓞 L)) :
    fixedFieldMulEquiv H h • P = h • P := by sorry
