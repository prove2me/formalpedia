-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeClosed_eq_zero_of_pairing
-- name    : GlobalTheory.CompanionTheory.HodgeClosed.eq_zero_of_pairing
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:25:20.464376+00:00
-- url     : https://prove2.me/theorems/95abbebd-4ba2-49e0-a244-13a6659d90df
-- title:
--   Hodge Closed: eq zero of pairing
-- statement:
--   The Hodge Closed construction uses the eq zero of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedStOfTwoFormCohSt.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedStOfTwoFormCohSt.lean#L27-L37

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedStOfTwoFormCohSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeClosed
variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem GlobalTheory.CompanionTheory.HodgeClosed.eq_zero_of_pairing [Module.Finite R M] [Module.Projective R M] (t : ⋀[R]^2 M)
    (h : ∀ v : Fin 2 → Module.Dual R M, exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 v) t = 0) :
    t = 0 := by sorry
