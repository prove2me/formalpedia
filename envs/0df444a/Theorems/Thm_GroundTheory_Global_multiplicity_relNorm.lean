-- Prove2me | Theorems.Thm_GroundTheory_Global_multiplicity_relNorm
-- name    : GroundTheory.Global.multiplicity_relNorm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:31.485141+00:00
-- url     : https://prove2.me/theorems/e1ed91e7-d8c5-48e6-9bcf-f0aad32e8b9c
-- title:
--   Global: multiplicity rel Norm
-- statement:
--   The Global construction uses the multiplicity rel Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L101-L110

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

theorem GroundTheory.Global.multiplicity_relNorm (I : Ideal (𝓞 M)) (hI : I ≠ ⊥) :
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 K) I) =
      ∑ w : SemiLocal.PlacesOver M v,
        w.1.asIdeal.inertiaDeg (𝓞 K) * multiplicity w.1.asIdeal I := by sorry
