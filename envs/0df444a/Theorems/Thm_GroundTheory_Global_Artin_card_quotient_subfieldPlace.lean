-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_card_quotient_subfieldPlace
-- name    : GroundTheory.Global.Artin.card_quotient_subfieldPlace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:25.488538+00:00
-- url     : https://prove2.me/theorems/27de88e0-33a2-5e9b-9dd1-7966edc5ae64
-- title:
--   Artin: card quotient subfield Place
-- statement:
--   The Artin construction uses the card quotient subfield Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesFrobenius.lean#L109-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesFrobenius.lean#L109-L119

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
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
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))

theorem GroundTheory.Global.Artin.card_quotient_subfieldPlace (x : Gal(L/K)) :
    Nat.card (𝓞 (fixedField H) ⧸ (x • w.asIdeal).under (𝓞 (fixedField H))) =
      Nat.card (𝓞 K ⧸ (x • w.asIdeal).under (𝓞 K)) ^
        frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.asIdeal.inertia Gal(L/K)) x := by sorry
