-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_subfieldPlaceEquiv_mk
-- name    : GroundTheory.Global.Artin.subfieldPlaceEquiv_mk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:54.47007+00:00
-- url     : https://prove2.me/theorems/e4b9c029-9555-47c2-8f6d-53eef6bebfc3
-- title:
--   Artin: subfield Place Equiv mk
-- statement:
--   The Artin construction uses the subfield Place Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Places.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Places.lean#L107-L110

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobeniusEmbed
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
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

theorem GroundTheory.Global.Artin.subfieldPlaceEquiv_mk [w.asIdeal.LiesOver v.asIdeal] (x : Gal(L/K)) :
    (subfieldPlaceEquiv H v w (DoubleCoset.mk _ _ x) : HeightOneSpectrum (𝓞 (fixedField H))) =
      subfieldPlace H w x := by sorry

attribute [defeq] GroundTheory.Global.Artin.subfieldPlaceEquiv_mk
