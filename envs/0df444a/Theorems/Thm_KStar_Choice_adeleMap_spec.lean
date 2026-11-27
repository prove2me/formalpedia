-- Prove2me | Theorems.Thm_KStar_Choice_adeleMap_spec
-- name    : KStar.Choice.adeleMap_spec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:38.108929+00:00
-- url     : https://prove2.me/theorems/63e0467b-c407-5f3f-ac2d-4d78f15f7f5f
-- title:
--   Choice: adele Map spec
-- statement:
--   The Choice construction uses the adele Map spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/HeckeCharacterChoice/TendstoUnderCofinite.lean#L111-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/HeckeCharacterChoice/TendstoUnderCofinite.lean#L111-L152

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

theorem KStar.Choice.adeleMap_spec :
    Continuous (adeleMap K L) ∧ Function.Injective (adeleMap K L) ∧
      Continuous (infAdeleMap K L) ∧
      (∀ x : K, adeleMap K L (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧
      ∀ x : K, infAdeleMap K L (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) := by sorry
