-- Prove2me | Theorems.Thm_GlobalTheory_CycEigen_map_mulVec
-- name    : GlobalTheory.CycEigen.map_mulVec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:23:19.849802+00:00
-- url     : https://prove2.me/theorems/8335464f-9a40-5396-9d34-e9be98832f11
-- title:
--   Cyc Eigen: map mul Vec
-- statement:
--   The Cyc Eigen construction uses the map mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeBis.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeBis.lean#L32-L43

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

theorem GlobalTheory.CycEigen.map_mulVec {r : ℕ} (X : AddSubgroup C) (O : Set C) (hOX : ∀ o ∈ O, ∀ x ∈ X, o * x ∈ X)
    (T : C → C) (hadd : ∀ x ∈ X, ∀ x' ∈ X, T (x + x') = T x + T x')
    (hlin : ∀ o ∈ O, ∀ x ∈ X, T (o * x) = o * T x)
    (B : Matrix (Fin r) (Fin r) C) (hB : ∀ a b, B a b ∈ O) (v : Fin r → C) (hv : ∀ a, v a ∈ X) :
    (fun a => T (B.mulVec v a)) = B.mulVec fun a => T (v a) := by sorry
