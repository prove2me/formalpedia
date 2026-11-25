-- Prove2me | Theorems.Thm_GlobalTheory_CycPerturb_surj_of_lattice
-- name    : GlobalTheory.CycPerturb.surj_of_lattice
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:24:18.033989+00:00
-- url     : https://prove2.me/theorems/85d59235-37ea-4ffd-87a1-001e46308547
-- title:
--   Cyc Perturb: surj of lattice
-- statement:
--   The Cyc Perturb construction uses the surj of lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerGeneratorMatrixPerturbation.lean#L64-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerGeneratorMatrixPerturbation.lean#L64-L133

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycPerturb
variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem GlobalTheory.CycPerturb.surj_of_lattice [CompleteSpace C] {r : ℕ} (X : AddSubgroup C) (hX : IsClosed (X : Set C))
    (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C) (hg : ∀ x, ‖g x‖ = ‖x‖) (hgX : ∀ x ∈ X, g x ∈ X)
    (p : C) (π : C) (hπ : ‖π‖ < 1) (hgπ : g π = π) (hπX : ∀ x ∈ X, π * x ∈ X)
    (S : C → C) (hS : ∀ x ∈ X, S x ∈ X ∧ g (S x) - S x = p * x)
    (B : Matrix (Fin r) (Fin r) C) (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X)
    (w : Fin r → C) (hw : ∀ a, w a ∈ X) :
    ∃ y : Fin r → C, (∀ a, y a ∈ X) ∧
      ∀ a, g (y a) - y a + p * (π • B).mulVec (fun b => g (y b)) a = p * w a := by sorry
