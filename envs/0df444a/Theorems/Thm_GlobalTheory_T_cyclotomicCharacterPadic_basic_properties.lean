-- Prove2me | Theorems.Thm_GlobalTheory_T_cyclotomicCharacterPadic_basic_properties
-- name    : GlobalTheory.T.cyclotomicCharacterPadic_basic_properties
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:16.141044+00:00
-- url     : https://prove2.me/theorems/eb73d2bf-29b3-4c76-a024-edecb96a33ef
-- title:
--   T: cyclotomic Character Padic basic properties
-- statement:
--   The T construction uses the cyclotomic Character Padic basic properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicPropertiesStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicPropertiesStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicPropertiesStatement
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

theorem GlobalTheory.T.cyclotomicCharacterPadic_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ → (∀ g, ‖(χ g : ℚ_[l])‖ = 1) ∧ Continuous (fun g => (χ g : ℚ_[l])) ∧ ∀ (K : FinExt l) (g : GQ l), g ∈ (K0 K).fixingSubgroup → ((∀ j : ℕ, g ∈ Gj K j ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) ∧ (g ∈ Hinf K ↔ χ g = 1)) := by sorry
