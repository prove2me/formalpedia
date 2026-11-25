-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_main
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.main
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:44.893845+00:00
-- url     : https://prove2.me/theorems/21c05a68-b888-4a72-b5bf-56a269c23e65
-- title:
--   Box Index: main
-- statement:
--   The Box Index construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean#L151-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean#L151-L163

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV

theorem GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (c c' : Fin n → Fin n → F), (∀ a b, c a b ≠ 0) → (∀ a b, c' a b ≠ 0) → (∀ a b, ∃ o ∈ O, c' a b = c a b * o) → (((boxAdd O β c').relIndex (boxAdd O β c) : ℕ) : ℝ) = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => β p.1 ≤ β p.2), nrm (c p.1 p.2) / nrm (c' p.1 p.2) := by sorry
