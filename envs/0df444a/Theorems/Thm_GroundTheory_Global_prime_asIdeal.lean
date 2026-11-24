-- Prove2me | Theorems.Thm_GroundTheory_Global_prime_asIdeal
-- name    : GroundTheory.Global.prime_asIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:57.832543+00:00
-- url     : https://prove2.me/theorems/d2dd71b6-c747-4f7d-8ad3-39504fb8ddfc
-- title:
--   Global: prime as Ideal
-- statement:
--   The Global construction uses the prime as Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L28-L30

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

theorem GroundTheory.Global.prime_asIdeal {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) :
    Prime u.asIdeal := by sorry
