-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_mix_tmul
-- name    : GlobalTheory.CompanionTheory.HypWedge.mix_tmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:29.88279+00:00
-- url     : https://prove2.me/theorems/ed9d7189-2058-4b83-8b8a-7ce997d94fa4
-- title:
--   Hyp Wedge: mix tmul
-- statement:
--   The Hyp Wedge construction uses the mix tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L77-L78

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R M N V W : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem GlobalTheory.CompanionTheory.HypWedge.mix_tmul (σ : V →ₗ[R] M) (k : W →ₗ[R] M) (v : V) (w : W) :
    mix σ k (v ⊗ₜ w) = wB R M (σ v) (k w) := by sorry
