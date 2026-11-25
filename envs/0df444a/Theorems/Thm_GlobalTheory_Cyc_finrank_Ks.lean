-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_finrank_Ks
-- name    : GlobalTheory.Cyc.finrank_Ks
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:34:22.016822+00:00
-- url     : https://prove2.me/theorems/69cfcdfa-3bc8-48a7-b133-e8bb334c1d09
-- title:
--   Cyc: finrank Ks
-- statement:
--   The Cyc construction uses the finrank Ks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankCyclotomicExtAndCyclotomicCharSurjective.lean#L122-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankCyclotomicExtAndCyclotomicCharSurjective.lean#L122-L133

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

theorem GlobalTheory.Cyc.finrank_Ks (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) :
    Module.finrank ℚ_[l] ↥(Ks K j) =
      Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1)) := by sorry
