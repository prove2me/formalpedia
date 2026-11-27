-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_inertia_fixedField_smul_eq
-- name    : GroundTheory.Global.Artin.inertia_fixedField_smul_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:55:41.492736+00:00
-- url     : https://prove2.me/theorems/dc7ff831-07df-49ec-a71a-eb7efa9c2f86
-- title:
--   Artin: inertia fixed Field smul eq
-- statement:
--   The Artin construction uses the inertia fixed Field smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean#L76-L82

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

theorem GroundTheory.Global.Artin.inertia_fixedField_smul_eq (w : HeightOneSpectrum (𝓞 L)) (x : Gal(L/K)) :
    (x • w.asIdeal).inertia Gal(L/fixedField H) =
      ((MulAut.conj x • w.asIdeal.inertia Gal(L/K) : Subgroup Gal(L/K)).subgroupOf H).map
        (fixedFieldMulEquiv H).toMonoidHom := by sorry
