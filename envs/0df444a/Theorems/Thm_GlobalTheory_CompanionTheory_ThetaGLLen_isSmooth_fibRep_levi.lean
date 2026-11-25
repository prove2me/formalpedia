-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_isSmooth_fibRep_levi
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_levi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:42:44.99858+00:00
-- url     : https://prove2.me/theorems/89323157-f47b-48e5-a1e0-27db6e6ad6d0
-- title:
--   Theta GLLen: is Smooth fib Rep levi
-- statement:
--   The Theta GLLen construction uses the is Smooth fib Rep levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FibreRepresentationSmooth.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FibreRepresentationSmooth.lean#L71-L77

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmooth
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

theorem GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_levi (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) (κ : ℕ) :
    IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by sorry
