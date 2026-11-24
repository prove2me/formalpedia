-- Prove2me | Theorems.Thm_GlobalTheory_T_quadratic_unramified_iff_isPrime_map_or_ncard_primesOver_two
-- name    : GlobalTheory.T.quadratic_unramified_iff_isPrime_map_or_ncard_primesOver_two
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:56:52.19604+00:00
-- url     : https://prove2.me/theorems/48e575e7-b5ad-4df5-b929-e3cc47cd4660
-- title:
--   T: quadratic unramified iff is Prime map or ncard primes Over two
-- statement:
--   The T construction uses the quadratic unramified iff is Prime map or ncard primes Over two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuadraticUnramifiedIffInertOrSplitStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuadraticUnramifiedIffInertOrSplitStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuadraticUnramifiedIffInertOrSplit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuadraticUnramifiedIffInertOrSplitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.quadratic_unramified_iff_isPrime_map_or_ncard_primesOver_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), ((∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔ ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime ∨ (v.asIdeal.primesOver (𝓞 E)).ncard = 2)) := by sorry
