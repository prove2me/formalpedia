-- Prove2me | Theorems.Thm_GlobalTheory_exists_finset_boundedBasis
-- name    : GlobalTheory.exists_finset_boundedBasis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:41.028839+00:00
-- url     : https://prove2.me/theorems/5e1291cf-7204-4adb-bd27-81bb558965ef
-- title:
--   Global Theory: exists finset bounded Basis
-- statement:
--   The Global Theory construction uses the exists finset bounded Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L393-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L393-L429

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

theorem GlobalTheory.exists_finset_boundedBasis (X : DataX E r) {B : ℝ} (hB : 0 ≤ B) :
    ∃ V : Finset (Fin r → Fin r → E), (∀ v ∈ V, IsBoundedBasis X B v) ∧
      (∀ v, IsBoundedBasis X B v →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i) ∧
      (V.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
        ((X.NA : ℝ) * X.NC * r * B) ^ (2 * fdeg E * r ^ 2) * (X.g : ℝ) ^ (2 * fdeg E * r ^ 2) := by sorry
