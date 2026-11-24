-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeClosed_pairing_map
-- name    : GlobalTheory.CompanionTheory.HodgeClosed.pairing_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:25:38.456434+00:00
-- url     : https://prove2.me/theorems/92bc792c-ee1c-45a5-b7cc-24cec10719de
-- title:
--   Hodge Closed: pairing map
-- statement:
--   The Hodge Closed construction uses the pairing map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedStOfTwoFormCohSt.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedStOfTwoFormCohSt.lean#L17-L25

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

theorem GlobalTheory.CompanionTheory.HodgeClosed.pairing_map (v : Fin 2 → Module.Dual R N) (g : M →ₗ[R] N) (t : ⋀[R]^2 M) :
    exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 v) (exteriorPower.map 2 g t) =
      exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 fun i ↦ v i ∘ₗ g) t := by sorry
