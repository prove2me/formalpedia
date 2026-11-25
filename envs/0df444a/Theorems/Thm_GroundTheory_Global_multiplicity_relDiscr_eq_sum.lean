-- Prove2me | Theorems.Thm_GroundTheory_Global_multiplicity_relDiscr_eq_sum
-- name    : GroundTheory.Global.multiplicity_relDiscr_eq_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:04.674903+00:00
-- url     : https://prove2.me/theorems/f2b9cd15-efa6-429f-b754-aecf0cf1524a
-- title:
--   Global: multiplicity rel Discr eq sum
-- statement:
--   The Global construction uses the multiplicity rel Discr eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L112-L116

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
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
open IsDedekindDomain NumberField Module
open GroundTheory GroundTheory.Global
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
variable (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.multiplicity_relDiscr_eq_sum :
    multiplicity v.asIdeal (relDiscr K M) =
      ∑ w : SemiLocal.PlacesOver M v,
        w.1.asIdeal.inertiaDeg (𝓞 K) * multiplicity w.1.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) := by sorry
