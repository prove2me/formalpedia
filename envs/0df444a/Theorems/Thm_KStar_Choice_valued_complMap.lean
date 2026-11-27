-- Prove2me | Theorems.Thm_KStar_Choice_valued_complMap
-- name    : KStar.Choice.valued_complMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:21.39743+00:00
-- url     : https://prove2.me/theorems/2672ffec-aa41-515b-8da0-4b6acb981e5c
-- title:
--   Choice: valued compl Map
-- statement:
--   The Choice construction uses the valued compl Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/HeckeCharacterChoice/TendstoUnderCofinite.lean#L86-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/HeckeCharacterChoice/TendstoUnderCofinite.lean#L86-L109

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_TendstoUnderCofinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open KStar KStar.Choice
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K L)

theorem KStar.Choice.valued_complMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (x : v.adicCompletion K) :
    Valued.v (complMap v w x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by sorry
