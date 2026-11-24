-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_local_chart_at_prime
-- name    : GlobalTheory.T.exists_local_chart_at_prime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:36.412909+00:00
-- url     : https://prove2.me/theorems/adb69ac1-0200-42e8-a887-04a341b05049
-- title:
--   T: exists local chart at prime
-- statement:
--   The T construction uses the exists local chart at prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsLocalChartAtPrimeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsLocalChartAtPrimeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLocalChartAtPrime
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLocalChartAtPrimeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_local_chart_at_prime : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (g : ℕ), e ≫ s = 𝟙 _ → SmoothOfRelativeDimension g s → ∀ p : PrimeSpectrum R, ∃ (r : R) (A C : Type) (_ : CommRing A) (_ : CommRing C) (_ : Algebra C A) (_ : Algebra A (Localization.Away r)) (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R), r ∉ p.asIdeal ∧ IsOpenImmersion j ∧ Mono k ∧ j ≫ s = spMap (algebraMap C A) ≫ k ∧ spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e ∧ Module.Free A (KaehlerDifferential C A) ∧ Module.Finite A (KaehlerDifferential C A) ∧ Module.finrank A (KaehlerDifferential C A) = g := by sorry
