-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_decomp
-- name    : GlobalTheory.CompanionTheory.HypWedge.decomp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:22.151472+00:00
-- url     : https://prove2.me/theorems/1aa0c98e-4fe9-5a1e-adf8-8f72ec12ab5a
-- title:
--   Hyp Wedge: decomp
-- statement:
--   The Hyp Wedge construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L80-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L80-L106

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

theorem GlobalTheory.CompanionTheory.HypWedge.decomp (σ : V →ₗ[R] M) (k : W →ₗ[R] M) (hs : ∀ a, ∃ v w, a = σ v + k w) (x : ⋀[R]^2 M) :
    ∃ y u z, x = exteriorPower.map 2 σ y + mix σ k u + exteriorPower.map 2 k z := by sorry
