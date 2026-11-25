-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_aeval_dual
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.aeval_dual
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:11.066429+00:00
-- url     : https://prove2.me/theorems/ed2c68df-14b2-4186-a413-4450b871b37c
-- title:
--   Reg: aeval dual
-- statement:
--   The Reg construction uses the aeval dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L264-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L264-L301

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.aeval_dual (σ : Type) [Fintype σ] (w v : σ → ℂ) (g : MvPolynomial σ ℚ) :
    (aeval (fun q => (TrivSqZeroExt.inl (w q) + TrivSqZeroExt.inr (v q) : TrivSqZeroExt ℂ ℂ)) g).fst =
        eval w (map (algebraMap ℚ ℂ) g) ∧
    (aeval (fun q => (TrivSqZeroExt.inl (w q) + TrivSqZeroExt.inr (v q) : TrivSqZeroExt ℂ ℂ)) g).snd =
        ∑ q, eval w (pderiv q (map (algebraMap ℚ ℂ) g)) * v q := by sorry
