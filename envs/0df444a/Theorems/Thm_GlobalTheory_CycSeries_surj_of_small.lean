-- Prove2me | Theorems.Thm_GlobalTheory_CycSeries_surj_of_small
-- name    : GlobalTheory.CycSeries.surj_of_small
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:25:01.279827+00:00
-- url     : https://prove2.me/theorems/dd8e066c-4e7e-432a-b88f-451dea7ec73f
-- title:
--   Cyc Series: surj of small
-- statement:
--   The Cyc Series construction uses the surj of small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeTer.lean#L56-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeTer.lean#L56-L117

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycSeries
variable {C : Type} [NormedField C]

theorem GlobalTheory.CycSeries.surj_of_small [CompleteSpace C] {r : ℕ} (X : AddSubgroup C) (hX : IsClosed (X : Set C))
    (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C) (hg : Continuous g) (hgX : ∀ x ∈ X, g x ∈ X)
    (p q : C) (hq1 : ‖q‖ < 1) (hgq : g q = q) (hqX : ∀ x ∈ X, q * x ∈ X) (S : C → C)
    (hS : ∀ x ∈ X, S x ∈ X ∧ g (S x) - S x = p * x)
    (B : Matrix (Fin r) (Fin r) C)
    (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X) (w : Fin r → C) (hw : ∀ a, w a ∈ X) :
    ∃ y : Fin r → C, (∀ a, y a ∈ X) ∧
      ∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = p * w a := by sorry
