-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_fixedFieldMulEquiv_smul_ringOfIntegers
-- name    : GroundTheory.Global.Artin.fixedFieldMulEquiv_smul_ringOfIntegers
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:47:38.415879+00:00
-- url     : https://prove2.me/theorems/848b79f5-c817-420b-8ad2-97b54014028f
-- title:
--   Artin: fixed Field Mul Equiv smul ring Of Integers
-- statement:
--   The Artin construction uses the fixed Field Mul Equiv smul ring Of Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L29-L31

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

theorem GroundTheory.Global.Artin.fixedFieldMulEquiv_smul_ringOfIntegers (h : H) (y : 𝓞 L) :
    fixedFieldMulEquiv H h • y = h • y := by sorry
