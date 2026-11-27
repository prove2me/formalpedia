-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_ResEtaPow_triv_of_even
-- name    : GlobalTheory.WeilM.ResEtaPow.triv_of_even
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:42.089223+00:00
-- url     : https://prove2.me/theorems/3699d016-7d82-5a15-a1e7-95d5247029c3
-- title:
--   Res Eta Pow: triv of even
-- statement:
--   The Res Eta Pow construction uses the triv of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L412-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L412-L414

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
variable (c)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
omit [Invertible (2 : R)]

theorem GlobalTheory.WeilM.ResEtaPow.triv_of_even {K : Subgroup Rˣ} {χ : Eˣ →* Circle} {n : ℕ} (hχ : ResEtaPow K χ n) (hn : Even n)
    (a : Rˣ) : χ (Units.map (algebraMap R E : R →* E) a) = 1 := by sorry
