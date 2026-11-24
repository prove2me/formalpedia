-- Prove2me | Theorems.Thm_GroundTheory_Global_emultiplicity_asIdeal_of_isMaximal
-- name    : GroundTheory.Global.emultiplicity_asIdeal_of_isMaximal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:59.875902+00:00
-- url     : https://prove2.me/theorems/7eafb1be-28be-441e-bf53-d98baa4f78a0
-- title:
--   Global: emultiplicity as Ideal of is Maximal
-- statement:
--   The Global construction uses the emultiplicity as Ideal of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L32-L42

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

theorem GroundTheory.Global.emultiplicity_asIdeal_of_isMaximal {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (p : Ideal (𝓞 F)) [hp : p.IsMaximal] :
    emultiplicity u.asIdeal p = if u.asIdeal = p then 1 else 0 := by sorry
