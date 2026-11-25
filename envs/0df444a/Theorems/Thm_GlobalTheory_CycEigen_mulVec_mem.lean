-- Prove2me | Theorems.Thm_GlobalTheory_CycEigen_mulVec_mem
-- name    : GlobalTheory.CycEigen.mulVec_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:24:28.68725+00:00
-- url     : https://prove2.me/theorems/762d458e-607f-4c23-b9e7-0048c7ba061a
-- title:
--   Cyc Eigen: mul Vec mem
-- statement:
--   The Cyc Eigen construction uses the mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeBis.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeBis.lean#L25-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {C : Type} [NormedField C] [IsUltrametricDist C]
omit [IsUltrametricDist C]

theorem GlobalTheory.CycEigen.mulVec_mem {r : ℕ} (X : AddSubgroup C) (B : Matrix (Fin r) (Fin r) C)
    (hB : ∀ a b, ∀ x ∈ X, B a b * x ∈ X) (v : Fin r → C) (hv : ∀ a, v a ∈ X) (a : Fin r) :
    B.mulVec v a ∈ X := by sorry
