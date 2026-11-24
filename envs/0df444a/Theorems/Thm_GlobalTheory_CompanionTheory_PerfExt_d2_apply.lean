-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_d2_apply
-- name    : GlobalTheory.CompanionTheory.PerfExt.d2_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:35.178232+00:00
-- url     : https://prove2.me/theorems/3027f114-a526-4a72-8eff-101a0f8a80c3
-- title:
--   Perf Ext: d2 apply
-- statement:
--   The Perf Ext construction uses the d2 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/D2Apply.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/D2Apply.lean#L89-L92

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfExt

theorem GlobalTheory.CompanionTheory.PerfExt.d2_apply {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (z : C2 F)
    {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ + z T T' T''' φ (ψ ≫ χ) -
      mp F χ (z T T' T'' φ ψ) := by sorry
