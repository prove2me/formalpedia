-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_inertiaDeg_subfieldPlace
-- name    : GroundTheory.Global.Artin.inertiaDeg_subfieldPlace
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:01.447731+00:00
-- url     : https://prove2.me/theorems/b32ca4e0-9c63-4fa4-82e3-8191e7d546e2
-- title:
--   Artin: inertia Deg subfield Place
-- statement:
--   The Artin construction uses the inertia Deg subfield Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesFrobenius.lean#L58-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesFrobenius.lean#L58-L89

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

theorem GroundTheory.Global.Artin.inertiaDeg_subfieldPlace (x : Gal(L/K)) :
    (subfieldPlace H w x).asIdeal.inertiaDeg (𝓞 K) =
      frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.asIdeal.inertia Gal(L/K)) x := by sorry
