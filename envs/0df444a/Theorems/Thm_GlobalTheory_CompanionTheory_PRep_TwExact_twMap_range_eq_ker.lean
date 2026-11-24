-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PRep_TwExact_twMap_range_eq_ker
-- name    : GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:04.471202+00:00
-- url     : https://prove2.me/theorems/59affc73-90bb-49a3-b474-8bcc4c428f73
-- title:
--   Tw Exact: tw Map range eq ker
-- statement:
--   The Tw Exact construction uses the tw Map range eq ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedJacquetExactSmooth.lean#L10-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedJacquetExactSmooth.lean#L10-L82

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_MirabolicDerivatives_TwistedKernels_TwKerLeComapOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwKerEqMapOfSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedJacquetExactSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.BZMir
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep GlobalTheory.CompanionTheory.PRep.TwExact

theorem GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker : ∀ {G V₁ V₂ V₃ : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
    (ρ₃ : Representation ℂ G V₃), IsSmooth ρ₁ → IsSmooth ρ₂ → IsSmooth ρ₃ →
    ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) →
    (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧
      IsCompact (L : Set G)) →
    ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v))
      (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v)), LinearMap.range f = LinearMap.ker g →
    LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg) := by sorry
