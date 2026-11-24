-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_eq_zero_of_vecMul
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.eq_zero_of_vecMul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:42:44.599+00:00
-- url     : https://prove2.me/theorems/57db27e5-3efb-4dc8-a677-e687f7bef265
-- title:
--   Theta GLLen: eq zero of vec Mul
-- statement:
--   The Theta GLLen construction uses the eq zero of vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/OmegaEquivInducedFibre.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/OmegaEquivInducedFibre.lean#L108-L114

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.eq_zero_of_vecMul (e : c ⊕ d ≃ b) {κ : ℕ} (hκ : κ = Fintype.card c) (y : RankIn k a c {κ})
    (v : c → k) (h : v ᵥ* y.1 = 0) : v = 0 := by sorry
