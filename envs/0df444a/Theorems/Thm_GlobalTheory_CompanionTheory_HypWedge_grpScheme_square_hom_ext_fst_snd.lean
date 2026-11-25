-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_grpScheme_square_hom_ext_fst_snd
-- name    : GlobalTheory.CompanionTheory.HypWedge.grpScheme_square_hom_ext_fst_snd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:21:23.908799+00:00
-- url     : https://prove2.me/theorems/3f08c075-838c-4546-988f-690585ec8e35
-- title:
--   Hyp Wedge: grp Scheme square hom ext fst snd
-- statement:
--   The Hyp Wedge construction uses the grp Scheme square hom ext fst snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L40-L47

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

theorem GlobalTheory.CompanionTheory.HypWedge.grpScheme_square_hom_ext_fst_snd {f g : ⋀[R]^2 M →ₗ[R] N}
    (h : ∀ a b, f (exteriorPower.ιMulti R 2 ![a, b]) = g (exteriorPower.ιMulti R 2 ![a, b])) : f = g := by sorry
