-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_rankAtStalk_of_locally
-- name    : GlobalTheory.AugCot.rankAtStalk_of_locally
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:21.799321+00:00
-- url     : https://prove2.me/theorems/c3f0c295-4245-4be0-a820-7430b74cb0e8
-- title:
--   Aug Cot: rank At Stalk of locally
-- statement:
--   The Aug Cot construction uses the rank At Stalk of locally property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L749-L753
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L749-L753

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
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) {n : ℕ}

theorem GlobalTheory.AugCot.rankAtStalk_of_locally
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (p : PrimeSpectrum R) : Module.rankAtStalk (AugCot ε) p = n := by sorry
