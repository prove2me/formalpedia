-- Prove2me | Theorems.Thm_GroundTheory_Global_Kummer_exists_mul_pow_integral_notMem
-- name    : GroundTheory.Global.Kummer.exists_mul_pow_integral_notMem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:39:47.558167+00:00
-- url     : https://prove2.me/theorems/a754b951-73e6-4c0b-8f14-a6b0f16e75f0
-- title:
--   Kummer: exists mul pow integral not Mem
-- statement:
--   The Kummer construction uses the exists mul pow integral not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Unramified.lean#L11-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Unramified.lean#L11-L43

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Unramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Global.Kummer
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.Kummer.exists_mul_pow_integral_notMem (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0)
    (a : Kˣ) (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) :
    ∃ c : K, c ≠ 0 ∧ ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = a * c ^ n ∧ b ∉ v.asIdeal := by sorry
