-- Prove2me | Theorems.Thm_GroundTheory_Global_Kummer_isUnramifiedIn_of_pow_eq
-- name    : GroundTheory.Global.Kummer.isUnramifiedIn_of_pow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:26.141878+00:00
-- url     : https://prove2.me/theorems/f78e2ea0-16c7-43ff-ae1b-6737ef66e9aa
-- title:
--   Kummer: is Unramified In of pow eq
-- statement:
--   The Kummer construction uses the is Unramified In of pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Unramified.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Unramified.lean#L121-L126

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
variable {M : Type*} [Field M] [NumberField M] [Algebra K M]

theorem GroundTheory.Global.Kummer.isUnramifiedIn_of_pow_eq {n : ℕ} (a : Kˣ) {α : M}
    (hα : α ^ n = algebraMap K M a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) :
    Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal := by sorry
