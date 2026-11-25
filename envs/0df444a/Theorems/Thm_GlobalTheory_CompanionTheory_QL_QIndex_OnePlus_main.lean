-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_OnePlus_main
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.OnePlus.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:28.332042+00:00
-- url     : https://prove2.me/theorems/f7f1ed74-1782-47ff-89ce-30b1917078c3
-- title:
--   One Plus: main
-- statement:
--   The One Plus construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemBoxLatticeIffCongruence.lean#L59-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemBoxLatticeIffCongruence.lean#L59-L112

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemBoxLatticeIffCongruence
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.OnePlus

theorem GlobalTheory.CompanionTheory.QL.QIndex.OnePlus.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (Q : Subgroup (GL (Fin n) F)), (∀ g, g ∈ Q ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β) → ∀ T : ℕ, 1 ≤ T → ∀ x : Matrix (Fin n) (Fin n) F, x ∈ boxAdd O β (fun _ _ => ϖ ^ T) ↔ ∃ p ∈ (congGL O (ϖ ^ T) n).subgroupOf Q, ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + x := by sorry
