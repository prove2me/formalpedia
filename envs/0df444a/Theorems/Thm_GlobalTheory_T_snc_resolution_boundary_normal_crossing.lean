-- Prove2me | Theorems.Thm_GlobalTheory_T_snc_resolution_boundary_normal_crossing
-- name    : GlobalTheory.T.snc_resolution_boundary_normal_crossing
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:49:11.605812+00:00
-- url     : https://prove2.me/theorems/f0985f1e-d309-4654-b9ac-820fbcf6f377
-- title:
--   T: snc resolution boundary normal crossing
-- statement:
--   The T construction uses the snc resolution boundary normal crossing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionBoundaryNormalCrossingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionBoundaryNormalCrossingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionBoundaryNormalCrossing
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionBoundaryNormalCrossingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.snc_resolution_boundary_normal_crossing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, ∃ d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)), (∃ O : Set (SncRes.Pts (pC (mCoordIdeal y))), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src (pC (mCoordIdeal y)) p ∧ ∀ k, SncRes.comp (pC (mCoordIdeal y)) (pC J) k ∩ O = {x' ∈ O | ∃ l, d.σ l = some k ∧ eval (SncRes.coord (pC (mCoordIdeal y)) p x') (d.r l) = 0}) ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), ReciprocityTheory.AnForm.R.IsMultiHomog f a → f ∉ pC (mCoordIdeal y) → (∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)), eval z f = 0 → z ∈ ReciprocityTheory.AnForm.R.conePts (pC J)) → ∃ u : ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x), IsUnit u ∧ algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (bind₁ (SncRes.lift p) f) = u * ∏ l ∈ d.J, algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (d.r l) ^ (d.σ l).elim 0 (fun k => SncRes.ordAlong (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k) (pC (mCoordIdeal y)) f) := by sorry
