-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_exists_chi_eq
-- name    : GlobalTheory.Cyc.exists_chi_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:26.94286+00:00
-- url     : https://prove2.me/theorems/111e5abf-df99-4533-8740-351446b2ac07
-- title:
--   Cyc: exists chi eq
-- statement:
--   The Cyc construction uses the exists chi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankCyclotomicExtAndCyclotomicCharSurjective.lean#L184-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankCyclotomicExtAndCyclotomicCharSurjective.lean#L184-L207

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.exists_chi_eq (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) : ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by sorry
