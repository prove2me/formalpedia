-- Prove2me | Theorems.Thm_GlobalTheory_CharForm_apply_eq_of_periodic
-- name    : GlobalTheory.CharForm.apply_eq_of_periodic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:26.425899+00:00
-- url     : https://prove2.me/theorems/70635984-8bca-451c-bb47-687f938f1b93
-- title:
--   Char Form: apply eq of periodic
-- statement:
--   The Char Form construction uses the apply eq of periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEqMulApplyZero.lean#L64-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEqMulApplyZero.lean#L64-L114

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEqMulApplyZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
noncomputable section
open scoped Classical Topology
open GlobalTheory GlobalTheory.CharForm
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem GlobalTheory.CharForm.apply_eq_of_periodic {C : Set (X → ℂ)} (a : (X → ℂ) →ₗ[ℂ] ℂ)
    (ha : ∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g)
    (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X))
    (hUk : ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) (hper : ∀ x, ∀ u ∈ U, g (x + u) = g x) :
    a g = g 0 * a (cosetInd U 0) := by sorry
