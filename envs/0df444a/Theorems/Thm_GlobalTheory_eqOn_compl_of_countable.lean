-- Prove2me | Theorems.Thm_GlobalTheory_eqOn_compl_of_countable
-- name    : GlobalTheory.eqOn_compl_of_countable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:38.327334+00:00
-- url     : https://prove2.me/theorems/d78d58a6-5b1c-4eb9-ad07-075ac3f525f8
-- title:
--   Global Theory: eq On compl of countable
-- statement:
--   The Global Theory construction uses the eq On compl of countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L15-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)

theorem GlobalTheory.eqOn_compl_of_countable {f g : ℂ → ℂ} {S : Set ℂ} (hS : S.Countable)
    (hf : AnalyticOnNhd ℂ f Sᶜ) (hg : AnalyticOnNhd ℂ g Sᶜ) {z : ℂ} (hz : z ∉ S)
    (h : f =ᶠ[𝓝 z] g) : Set.EqOn f g Sᶜ := by sorry
