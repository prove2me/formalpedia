-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_eq_of_exp_mul_pow_eq
-- name    : GroundTheory.Global.SemiLocal.eq_of_exp_mul_pow_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:50.691421+00:00
-- url     : https://prove2.me/theorems/375672d0-5a8a-44df-bb53-7b1949c18414
-- title:
--   Semi Local: eq of exp mul pow eq
-- statement:
--   The Semi Local construction uses the eq of exp mul pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L183-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L183-L189

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
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
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
variable {ι : Type*} [Fintype ι]

theorem GroundTheory.Global.SemiLocal.eq_of_exp_mul_pow_eq {e i i' : ℕ} (hi : i < e) (hi' : i' < e) {a b : ℤᵐ⁰} (ha : a ≠ 0)
    (hb : b ≠ 0) (h : exp (-(i : ℤ)) * a ^ e = exp (-(i' : ℤ)) * b ^ e) : i = i' := by sorry
