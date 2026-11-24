-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_tmul
-- name    : GlobalTheory.CompanionTheory.WedgeOf.wedgeT_tmul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:07.814941+00:00
-- url     : https://prove2.me/theorems/36ce2e50-3478-4eff-a38a-4c9012a989d1
-- title:
--   Wedge Of: wedge T tmul
-- statement:
--   The Wedge Of construction uses the wedge T tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IotaQInjective.lean#L66-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IotaQInjective.lean#L66-L66

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] (V : Type) [AddCommGroup V] [Module R V]

theorem GlobalTheory.CompanionTheory.WedgeOf.wedgeT_tmul (a b : V) : wedgeT (R := R) V (a ⊗ₜ b) = exteriorPower.ιMulti R 2 ![a, b] := by sorry
