-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_fibChar_fst
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.fibChar_fst
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:42:30.785182+00:00
-- url     : https://prove2.me/theorems/d2875b2f-83da-4617-bce7-b023ab54edfc
-- title:
--   Theta GLLen: fib Char fst
-- statement:
--   The Theta GLLen construction uses the fib Char fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/OmegaEquivInducedFibre.lean#L133-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/OmegaEquivInducedFibre.lean#L133-L137

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OmegaEquivInducedFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

theorem GlobalTheory.CompanionTheory.ThetaGLLen.fibChar_fst (e : c ⊕ d ≃ b) (μ : kˣ →* ℂˣ) (γ : GL a k) :
    fibChar a c d μ (γ, 1, 1) = omChar a b μ (γ, 1) := by sorry
