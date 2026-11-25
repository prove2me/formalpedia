-- Prove2me | Theorems.Thm_GlobalTheory_exists_finset_types_of_bounded_bases
-- name    : GlobalTheory.exists_finset_types_of_bounded_bases
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:17.016133+00:00
-- url     : https://prove2.me/theorems/4aadae3d-30ab-5ff7-ad77-1b7613d18b4c
-- title:
--   Global Theory: exists finset types of bounded bases
-- statement:
--   The Global Theory construction uses the exists finset types of bounded bases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L431-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L431-L448

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.exists_finset_types_of_bounded_bases (X : DataX E r) {B : ℝ} (hB : 1 ≤ B) :
    ∃ V : Finset (Fin r → Fin r → E),
      (∀ v ∈ V, (∀ i, v i ∈ X.L') ∧ LinearIndependent E v ∧
        ∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B) ∧
      (∀ v : Fin r → Fin r → E, (∀ i, v i ∈ X.L') → LinearIndependent E v →
        (∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B) →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (w i)) ∧
      (V.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
        ((X.NA : ℝ) * X.NC * r * B) ^ (2 * fdeg E * r ^ 2) * (X.g : ℝ) ^ (2 * fdeg E * r ^ 2) ∧
      (V.card : ℝ) ≤ (3 * (X.NA : ℝ) * X.NC * X.g * r * B ^ 2) ^ (2 * fdeg E * r ^ 2) := by sorry
