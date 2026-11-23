-- Prove2me | Theorems.Thm_GroundTheory_Global_Kummer_isUnramifiedAt_of_pow_eq
-- name    : GroundTheory.Global.Kummer.isUnramifiedAt_of_pow_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:51.880847+00:00
-- url     : https://prove2.me/theorems/86904602-0ad3-400f-9db2-4c1f86d11f61
-- title:
--   Kummer: is Unramified At of pow eq
-- statement:
--   The Kummer construction uses the is Unramified At of pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Unramified.lean#L47-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Unramified.lean#L47-L110

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

theorem GroundTheory.Global.Kummer.isUnramifiedAt_of_pow_eq {n : ℕ} (a : Kˣ) {α : M} (hα : α ^ n = algebraMap K M a)
    (hgen : IntermediateField.adjoin K {α} = ⊤) (v : HeightOneSpectrum (𝓞 K))
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)))
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) P := by sorry
