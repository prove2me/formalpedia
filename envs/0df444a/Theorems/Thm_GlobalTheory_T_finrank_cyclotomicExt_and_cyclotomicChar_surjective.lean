-- Prove2me | Theorems.Thm_GlobalTheory_T_finrank_cyclotomicExt_and_cyclotomicChar_surjective
-- name    : GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:24.769497+00:00
-- url     : https://prove2.me/theorems/572e2c5f-27a2-4747-96a1-d0b29235fecc
-- title:
--   T: finrank cyclotomic Ext and cyclotomic Char surjective
-- statement:
--   The T construction uses the finrank cyclotomic Ext and cyclotomic Char surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjective
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), (∀ j : ℕ, 1 ≤ j → Module.finrank ℚ_[l] ↥(Ks K j) = Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1))) ∧ ∀ χ : GQ l →* ℚ_[l]ˣ, IsCyc χ → ∀ u : ℚ_[l], ‖u‖ = 1 → ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by sorry
