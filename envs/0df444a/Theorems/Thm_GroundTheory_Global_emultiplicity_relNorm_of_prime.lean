-- Prove2me | Theorems.Thm_GroundTheory_Global_emultiplicity_relNorm_of_prime
-- name    : GroundTheory.Global.emultiplicity_relNorm_of_prime
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:27.106001+00:00
-- url     : https://prove2.me/theorems/517cbbd3-702a-4dc9-a428-71b1b1bef123
-- title:
--   Global: emultiplicity rel Norm of prime
-- statement:
--   The Global construction uses the emultiplicity rel Norm of prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L46-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L46-L79

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

theorem GroundTheory.Global.emultiplicity_relNorm_of_prime (p : Ideal (𝓞 M)) (hp : Prime p) :
    emultiplicity v.asIdeal (Ideal.relNorm (𝓞 K) p) =
      ∑ w : SemiLocal.PlacesOver M v,
        (w.1.asIdeal.inertiaDeg (𝓞 K) : ℕ∞) * emultiplicity w.1.asIdeal p := by sorry
