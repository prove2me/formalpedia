-- Prove2me | Theorems.Thm_GlobalTheory_SmoothAdic_isSmoothAt_of_smooth_quotient_pow
-- name    : GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:29:23.73418+00:00
-- url     : https://prove2.me/theorems/cdc239bd-345f-4de0-b261-5085fc409fd5
-- title:
--   Smooth Adic: is Smooth At of smooth quotient pow
-- statement:
--   The Smooth Adic construction uses the is Smooth At of smooth quotient pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsSmoothAtOfSmoothModIdealPowers.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsSmoothAtOfSmoothModIdealPowers.lean#L8-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSmoothAtOfSmoothQuotientPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSmoothAtOfSmoothModIdealPowers
import Theorems.Thm_GlobalTheory_SmoothLimit_isSmoothAt_of_smooth_quotient_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmoothAdic
open TensorProduct IsLocalRing

theorem GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra.FiniteType R C], (∀ e : ℕ, Algebra.Smooth (R ⧸ I ^ (e + 1)) (TensorProduct R (R ⧸ I ^ (e + 1)) C)) → ∀ (q : Ideal C) [q.IsPrime], q.comap (algebraMap R C) = IsLocalRing.maximalIdeal R → Algebra.IsSmoothAt R q := by sorry
