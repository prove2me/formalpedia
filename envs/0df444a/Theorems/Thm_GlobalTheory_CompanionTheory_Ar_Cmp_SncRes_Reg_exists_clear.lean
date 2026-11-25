-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_exists_clear
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_clear
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:31:05.304352+00:00
-- url     : https://prove2.me/theorems/7c216c65-1bfc-5f0d-805e-b78e5e47239b
-- title:
--   Reg: exists clear
-- statement:
--   The Reg construction uses the exists clear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L111-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L111-L139

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_clear {σ Ω C : Type} [Field Ω] [CharZero Ω] [CommRing C] [Algebra ℚ C] (u : σ → Ω) (t : σ → C)
    (F : MvPolynomial σ ℚ) (a : Ω) (b : C) (ha : a * aeval u F = 1) (hb : b * aeval t F = 1)
    (h : MvPolynomial (Option σ) ℚ) :
    ∃ (n : ℕ) (g : MvPolynomial σ ℚ),
      aeval u F ^ n * aeval (fun o : Option σ => o.elim a u) h = aeval u g ∧
      aeval t F ^ n * aeval (fun o : Option σ => o.elim b t) h = aeval t g := by sorry
