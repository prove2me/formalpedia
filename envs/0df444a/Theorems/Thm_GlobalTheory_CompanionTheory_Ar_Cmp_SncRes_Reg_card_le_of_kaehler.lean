-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_card_le_of_kaehler
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.card_le_of_kaehler
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:43:23.900673+00:00
-- url     : https://prove2.me/theorems/22daf8c7-70c8-4612-8166-7e80f651f7c5
-- title:
--   Reg: card le of kaehler
-- statement:
--   The Reg construction uses the card le of kaehler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L329-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L329-L366

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.card_le_of_kaehler (σ : Type) [Fintype σ] (Ω : Type) [Field Ω] [CharZero Ω] (u : σ → Ω)
    (V : Submodule ℂ (σ → ℂ)) (w : σ → ℂ) (F : MvPolynomial σ ℚ) (hF : aeval u F ≠ 0)
    (hFw : eval w (map (algebraMap ℚ ℂ) F) ≠ 0)
    (hker : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 → eval w (map (algebraMap ℚ ℂ) g) = 0)
    (hV : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 →
      (fun q => eval w (pderiv q (map (algebraMap ℚ ℂ) g))) ∈ V)
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (aeval u F)⁻¹ (Set.range u)))
    (e : ℕ) (z : Fin e → S)
    (hz : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) :
    Fintype.card σ ≤ Module.finrank ℂ V + e := by sorry
