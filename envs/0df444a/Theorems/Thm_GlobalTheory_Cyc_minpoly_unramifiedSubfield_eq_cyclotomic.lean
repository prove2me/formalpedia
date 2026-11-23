-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_minpoly_unramifiedSubfield_eq_cyclotomic
-- name    : GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:46.861806+00:00
-- url     : https://prove2.me/theorems/81faccb7-20c0-4f77-8b56-0917b59bbace
-- title:
--   Cyc: minpoly unramified Subfield eq cyclotomic
-- statement:
--   The Cyc construction uses the minpoly unramified Subfield eq cyclotomic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankCyclotomicExtAndCyclotomicCharSurjective.lean#L73-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankCyclotomicExtAndCyclotomicCharSurjective.lean#L73-L100

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

theorem GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) : minpoly ↥(K0 K) ζ = cyclotomic (l ^ j) ↥(K0 K) := by sorry
