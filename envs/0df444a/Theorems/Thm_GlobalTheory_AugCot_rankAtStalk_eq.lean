-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_rankAtStalk_eq
-- name    : GlobalTheory.AugCot.rankAtStalk_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:11.154557+00:00
-- url     : https://prove2.me/theorems/d4b11abd-0005-43da-8c24-119872b6c685
-- title:
--   Aug Cot: rank At Stalk eq
-- statement:
--   The Aug Cot construction uses the rank At Stalk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L676-L681
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L676-L681

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)

theorem GlobalTheory.AugCot.rankAtStalk_eq [Module.Finite A Ω[A⁄R]] [Module.Flat A Ω[A⁄R]] (p : PrimeSpectrum R) :
    Module.rankAtStalk (AugCot ε) p = Module.rankAtStalk Ω[A⁄R] (p.comap (ε : A →+* R)) := by sorry
