-- Prove2me | Theorems.Thm_GlobalTheory_CycSeries_inj_of_small
-- name    : GlobalTheory.CycSeries.inj_of_small
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:21:14.428802+00:00
-- url     : https://prove2.me/theorems/06438145-edb7-4eaf-b089-32ccfbb8b0cd
-- title:
--   Cyc Series: inj of small
-- statement:
--   The Cyc Series construction uses the inj of small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeTer.lean#L23-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeTer.lean#L23-L54

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

theorem GlobalTheory.CycSeries.inj_of_small {r : ℕ} (X : AddSubgroup C) (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C)
    (hgX : ∀ x ∈ X, g x ∈ X) (p q : C) (hp : p ≠ 0) (hq : q ≠ 0) (hq1 : ‖q‖ < 1) (hgq : g q = q)
    (S : C → C) (hS : ∀ x ∈ X, S x ∈ X ∧ S (g x - x) = p * x)
    (hlin : ∀ x ∈ X, S (p * q * x) = p * q * S x)
    (B : Matrix (Fin r) (Fin r) C) (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X)
    (y : Fin r → C) (hy : ∀ a, y a ∈ X)
    (h : ∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = 0) : y = 0 := by sorry
