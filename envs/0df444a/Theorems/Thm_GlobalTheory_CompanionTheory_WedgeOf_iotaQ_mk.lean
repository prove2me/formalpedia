-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_iotaQ_mk
-- name    : GlobalTheory.CompanionTheory.WedgeOf.iotaQ_mk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:35.603779+00:00
-- url     : https://prove2.me/theorems/841a8a23-c8cf-4c2d-9822-ecd1a9db7bea
-- title:
--   Wedge Of: iota Q mk
-- statement:
--   The Wedge Of construction uses the iota Q mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IotaQInjective.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IotaQInjective.lean#L24-L24

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
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem GlobalTheory.CompanionTheory.WedgeOf.iotaQ_mk (f : Z1 F) : iotaQ F (H1.mk F f) = Submodule.Quotient.mk f.1 := by sorry
