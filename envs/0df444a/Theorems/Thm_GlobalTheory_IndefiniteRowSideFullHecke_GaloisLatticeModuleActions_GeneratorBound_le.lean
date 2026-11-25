-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GaloisLatticeModuleActions_GeneratorBound_le
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.GeneratorBound.le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:47.091277+00:00
-- url     : https://prove2.me/theorems/f27d506c-9827-4cba-9ead-780df494d63f
-- title:
--   Generator Bound: le
-- statement:
--   The Generator Bound construction uses the le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/BlochKatoGeneratorBound.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/BlochKatoGeneratorBound.lean#L89-L93

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BlochKatoGeneratorBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.GeneratorBound.le {PD : PeriodData G Qp K₀ K B BdR} {T : LocLat G Qp LL O} {ϖ : O}
    (h : GeneratorBound PD T ϖ) :
    GeneratedByAtMost (latticeFiniteCohomology PD T.L) ((Module.finrank Qp K + 1) * Module.finrank O ↥T.L.T) := by sorry
