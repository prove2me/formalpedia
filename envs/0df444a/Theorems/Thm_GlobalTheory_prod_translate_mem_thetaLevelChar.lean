-- Prove2me | Theorems.Thm_GlobalTheory_prod_translate_mem_thetaLevelChar
-- name    : GlobalTheory.prod_translate_mem_thetaLevelChar
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:37:44.976573+00:00
-- url     : https://prove2.me/theorems/1d69472d-da78-4c62-85ae-2ac72a1091ad
-- title:
--   Global Theory: prod translate mem theta Level Char
-- statement:
--   The Global Theory construction uses the prod translate mem theta Level Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfSemicharacterMultiplier.lean#L98-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfSemicharacterMultiplier.lean#L98-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}

theorem GlobalTheory.prod_translate_mem_thetaLevelChar {κ : Type*} (s : Finset κ) {d : κ → ℕ}
    {F : κ → (ι → ℂ) → ℂ} (hF : ∀ i ∈ s, F i ∈ thetaLevelChar a b (d i) τ) (u : κ → ι → ℂ)
    (hu : ∑ i ∈ s, (d i : ℂ) • u i = 0) :
    (fun z => ∏ i ∈ s, F i (z + u i)) ∈ thetaLevelChar a b (∑ i ∈ s, d i) τ := by sorry
