-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_cyclotomicTowerLevelGenerator_properties
-- name    : GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:09:39.185554+00:00
-- url     : https://prove2.me/theorems/0ffa7183-9b0d-44ac-83aa-53f21d27b8af
-- title:
--   T: exists cyclotomic Tower Level Generator properties
-- statement:
--   The T construction uses the exists cyclotomic Tower Level Generator properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicTowerLevelGeneratorPropertiesStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicTowerLevelGeneratorPropertiesStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
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

theorem GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → (∃ g, IsGen χ K j g) ∧ ∀ g, IsGen χ K j g → ((∀ b : ℕ, IsGen χ K (j + b) (g ^ (l ^ b))) ∧ (∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n) ∧ (Gj K j : Set (GQ l)) ⊆ closure {x | ∃ h ∈ Hinf K, ∃ a : ℕ, x = h * g ^ a}) := by sorry
