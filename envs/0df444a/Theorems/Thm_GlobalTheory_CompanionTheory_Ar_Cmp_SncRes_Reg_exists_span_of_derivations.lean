-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_exists_span_of_derivations
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_span_of_derivations
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:31:14.955973+00:00
-- url     : https://prove2.me/theorems/1b7a6c87-151d-52cf-bbaa-2f9bbcada813
-- title:
--   Reg: exists span of derivations
-- statement:
--   The Reg construction uses the exists span of derivations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L223-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L223-L262

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_span_of_derivations (S : Type) [CommRing S] [Algebra ℚ S] (σ : Type) (u : σ → S) (e : ℕ)
    (z : Fin e → S)
    (hz : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) (ψ : S →ₐ[ℚ] ℂ) :
    ∃ b : Fin e → σ → ℂ, ∀ Φ : S →ₐ[ℚ] TrivSqZeroExt ℂ ℂ,
      (TrivSqZeroExt.fstHom ℚ ℂ ℂ).comp Φ = ψ →
      (fun q => (Φ (u q)).snd) ∈ Submodule.span ℂ (Set.range b) := by sorry
