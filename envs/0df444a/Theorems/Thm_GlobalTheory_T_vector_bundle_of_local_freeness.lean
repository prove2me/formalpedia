-- Prove2me | Theorems.Thm_GlobalTheory_T_vector_bundle_of_local_freeness
-- name    : GlobalTheory.T.vector_bundle_of_local_freeness
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:24.265213+00:00
-- url     : https://prove2.me/theorems/9b051021-bf01-498e-9ab8-c41de0276a68
-- title:
--   T: vector bundle of local freeness
-- statement:
--   The T construction uses the vector bundle of local freeness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VectorBundleOfLocalFreenessStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VectorBundleOfLocalFreenessStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VectorBundleOfLocalFreeness
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VectorBundleOfLocalFreenessStatement
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

theorem GlobalTheory.T.vector_bundle_of_local_freeness : ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (g : ℕ), (∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) ∧ Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) ∧ Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] W) = g) → VB R W g := by sorry
