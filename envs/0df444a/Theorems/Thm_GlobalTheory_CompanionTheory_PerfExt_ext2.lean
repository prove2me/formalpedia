-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_ext2
-- name    : GlobalTheory.CompanionTheory.PerfExt.ext2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:26.535623+00:00
-- url     : https://prove2.me/theorems/e7ef5ad6-1886-4454-8d4c-ed4dde437539
-- title:
--   Perf Ext: ext2
-- statement:
--   The Perf Ext construction uses the ext2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/D2Apply.lean#L107-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/D2Apply.lean#L107-L119

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
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} R'} [Finite C] [∀ T T' : C, Finite (T ⟶ T')]

theorem GlobalTheory.CompanionTheory.PerfExt.ext2 (m : BC F F') :
    Ext R R' (fun (f : C2 F) T T' T'' φ ψ ↦ m.α T'' (f T T' T'' φ ψ) : C2 F → C2 F') := by sorry
