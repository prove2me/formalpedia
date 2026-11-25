-- Prove2me | Theorems.Thm_GlobalTheory_CycEigen_eq_zero_of_small
-- name    : GlobalTheory.CycEigen.eq_zero_of_small
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:58.351271+00:00
-- url     : https://prove2.me/theorems/e0470899-6599-4312-bfde-7f2e506cabd8
-- title:
--   Cyc Eigen: eq zero of small
-- statement:
--   The Cyc Eigen construction uses the eq zero of small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeBis.lean#L45-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeBis.lean#L45-L79

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

theorem GlobalTheory.CycEigen.eq_zero_of_small {r : ℕ} (X : AddSubgroup C) (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (O : Set C)
    (hOX : ∀ o ∈ O, ∀ x ∈ X, o * x ∈ X) (T : C → C) (hTX : ∀ x ∈ X, T x ∈ X)
    (hadd : ∀ x ∈ X, ∀ x' ∈ X, T (x + x') = T x + T x')
    (hlin : ∀ o ∈ O, ∀ x ∈ X, T (o * x) = o * T x)
    (B : Matrix (Fin r) (Fin r) C) (hBO : ∀ a b, B a b ∈ O) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hB : ∀ a b, ‖B a b‖ ≤ c) (y : Fin r → C) (hy : ∀ a, y a ∈ X)
    (h : y = B.mulVec fun a => T (y a)) : y = 0 := by sorry
