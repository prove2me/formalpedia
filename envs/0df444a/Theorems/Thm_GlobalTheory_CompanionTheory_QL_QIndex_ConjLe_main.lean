-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_ConjLe_main
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.main
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:34.350893+00:00
-- url     : https://prove2.me/theorems/39725f1e-d660-4bac-8194-586e4dafc870
-- title:
--   Conj Le: main
-- statement:
--   The Conj Le construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DiagonalConjugateCongruenceBox.lean#L126-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DiagonalConjugateCongruenceBox.lean#L126-L168

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DiagonalConjugateCongruenceBox
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (Q : Subgroup (GL (Fin n) F)), (∀ g, g ∈ Q ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β) → ∀ T : ℕ, 1 ≤ T → ∀ d : Q, ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag → (∀ a b, ϖ ^ T * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) b b)⁻¹) ∈ O) → conjSub ((congGL O (ϖ ^ (2 * T)) n).subgroupOf Q) d ≤ (congGL O (ϖ ^ T) n).subgroupOf Q ∧ ∀ p ∈ (congGL O (ϖ ^ T) n).subgroupOf Q, (p ∈ conjSub ((congGL O (ϖ ^ (2 * T)) n).subgroupOf Q) d ↔ ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 ∈ boxAdd O β (lev ϖ T fun a => ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a)) := by sorry
