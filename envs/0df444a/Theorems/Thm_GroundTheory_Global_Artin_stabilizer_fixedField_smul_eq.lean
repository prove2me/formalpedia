-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_stabilizer_fixedField_smul_eq
-- name    : GroundTheory.Global.Artin.stabilizer_fixedField_smul_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:29.079671+00:00
-- url     : https://prove2.me/theorems/fa4810a5-adcb-5a3f-8ad4-994d2f1ae01d
-- title:
--   Artin: stabilizer fixed Field smul eq
-- statement:
--   The Artin construction uses the stabilizer fixed Field smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L66-L72

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

theorem GroundTheory.Global.Artin.stabilizer_fixedField_smul_eq (w : HeightOneSpectrum (𝓞 L)) (x : Gal(L/K)) :
    MulAction.stabilizer Gal(L/fixedField H) (x • w.asIdeal) =
      ((MulAut.conj x • MulAction.stabilizer Gal(L/K) w.asIdeal : Subgroup Gal(L/K)).subgroupOf
        H).map (fixedFieldMulEquiv H).toMonoidHom := by sorry
