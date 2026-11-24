-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_hasFiniteLength_coinv_of_ker
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_of_ker
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:20.474125+00:00
-- url     : https://prove2.me/theorems/784e57ca-d61d-4f67-8a31-3ebaea51bce3
-- title:
--   Theta GLLen: has Finite Length coinv of ker
-- statement:
--   The Theta GLLen construction uses the has Finite Length coinv of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoinvariantsFiniteOfSmoothLevi.lean#L14-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoinvariantsFiniteOfSmoothLevi.lean#L14-L31

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_of_ker {Γ G V U : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U] [Module ℂ U] (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ)
    (π : Representation ℂ G U) (Φ : V →ₗ[ℂ] U) (hint : ∀ g v, Φ (τ (1, g) v) = π g (Φ v))
    (hker : LinearMap.ker Φ = twRel (τ.comp (MonoidHom.inl Γ G)) ψ) (hπ : HasFiniteLength π) :
    HasFiniteLength (coinv τ ψ) := by sorry
