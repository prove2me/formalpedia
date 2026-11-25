-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_NearComp_comp_eq_near
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.comp_eq_near
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:36:17.308644+00:00
-- url     : https://prove2.me/theorems/65376e89-bca2-41e7-bf1b-1327cbdb6412
-- title:
--   Near Comp: comp eq near
-- statement:
--   The Near Comp construction uses the comp eq near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncChartRegularWithBoundaryChoice.lean#L72-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncChartRegularWithBoundaryChoice.lean#L72-L118

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSup
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartRegularWithBoundaryChoice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.comp_eq_near : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (x : SncRes.Pts P) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (σ : Fin e → Option (Fin (SncRes.rc P D))), IsMultiHomogIdeal P → IsMultiHomogIdeal D → x ∈ SncRes.src P p → (∀ h ∈ (SncRes.ideal P p), eval (SncRes.coord P p x) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (SncRes.coord P p x)) → ringKrullDim (locRing (SncRes.ideal P p) (SncRes.coord P p x)) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x)) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x))) (ptIdeal (SncRes.coord P p x)) → (∀ l, σ l = none ↔ l ∉ Jf) → (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)) → (∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval (SncRes.rep x) g = 0) → ∃ l ∈ Jf, σ l = some k) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∀ k, SncRes.comp P D k ∩ O = {x' ∈ O | ∃ l, σ l = some k ∧ eval (SncRes.coord P p x') (r l) = 0} := by sorry
