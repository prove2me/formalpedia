-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_hasFiniteLength_coinv_indSnd
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:02.244063+00:00
-- url     : https://prove2.me/theorems/d5d864d6-70fe-46af-accd-6319d9b9606f
-- title:
--   Theta GLLen: has Finite Length coinv ind Snd
-- statement:
--   The Theta GLLen construction uses the has Finite Length coinv ind Snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoinvariantsFiniteOfSmoothLevi.lean#L33-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoinvariantsFiniteOfSmoothLevi.lean#L33-L104

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], InductionFiniteLength k → ∀ (Γ W b c d : Type) [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (τ : Representation ℂ (Γ × (GL c k × GL d k)) W), IsSmooth (τ.comp (MonoidHom.inr Γ (GL c k × GL d k))) → ∀ ψ : Γ →* ℂˣ, Module.Finite ℂ (W ⧸ twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ) → HasFiniteLength (coinv (indSnd e τ) ψ) := by sorry
