-- Prove2me | Theorems.Thm_GroundTheory_Global_differentIdeal_le_pow_of_le_differentExponent
-- name    : GroundTheory.Global.differentIdeal_le_pow_of_le_differentExponent
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:49:43.313119+00:00
-- url     : https://prove2.me/theorems/ed6ae89b-d1b3-444b-8948-1c8ee51a38b4
-- title:
--   Global: different Ideal le pow of le different Exponent
-- statement:
--   The Global construction uses the different Ideal le pow of le different Exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L205-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L205-L229

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
open SemiLocal
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]

theorem GroundTheory.Global.differentIdeal_le_pow_of_le_differentExponent {n : ℕ}
    (hn : n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M)) :
    differentIdeal (𝓞 K) (𝓞 M) ≤ w.asIdeal ^ n := by sorry
