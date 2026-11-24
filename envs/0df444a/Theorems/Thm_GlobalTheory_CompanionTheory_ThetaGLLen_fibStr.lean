-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_fibStr
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.fibStr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:19.693831+00:00
-- url     : https://prove2.me/theorems/7eb3a974-0c31-4296-865c-f8acc129d828
-- title:
--   Theta GLLen: fib Str
-- statement:
--   The Theta GLLen construction uses the fib Str property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/OmegaEquivInducedFibre.lean#L139-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/OmegaEquivInducedFibre.lean#L139-L190

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.fibStr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b c d : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (κ : ℕ), κ = Fintype.card c → ∀ μ : kˣ →* ℂˣ,
    IsSmoothChar μ → Nonempty ((omegaOn a b μ {κ}).Equiv (indSnd e (fibRep a c d μ κ))) := by sorry
