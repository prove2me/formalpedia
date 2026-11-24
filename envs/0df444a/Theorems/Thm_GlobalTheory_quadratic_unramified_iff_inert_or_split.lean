-- Prove2me | Theorems.Thm_GlobalTheory_quadratic_unramified_iff_inert_or_split
-- name    : GlobalTheory.quadratic_unramified_iff_inert_or_split
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:15:13.648506+00:00
-- url     : https://prove2.me/theorems/44f39b42-4c79-4e1d-ac7a-2724a4a46b2d
-- title:
--   Global Theory: quadratic unramified iff inert or split
-- statement:
--   The Global Theory construction uses the quadratic unramified iff inert or split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuadraticUnramifiedIffInertOrSplit.lean#L10-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuadraticUnramifiedIffInertOrSplit.lean#L10-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuadraticUnramifiedIffInertOrSplit
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
open GlobalTheory
open scoped TensorProduct
open NumberField IsDedekindDomain

theorem GlobalTheory.quadratic_unramified_iff_inert_or_split (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    ((∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔
      ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime ∨
        (v.asIdeal.primesOver (𝓞 E)).ncard = 2)) := by sorry
