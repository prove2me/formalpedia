-- Prove2me | Theorems.Thm_GlobalTheory_Mass_LineGlue_sup_span_congr
-- name    : GlobalTheory.Mass.LineGlue.sup_span_congr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:50.730872+00:00
-- url     : https://prove2.me/theorems/1033cc94-2e18-54f8-b609-3a43f246b076
-- title:
--   Line Glue: sup span congr
-- statement:
--   The Line Glue construction uses the sup span congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianLatticesGluedAlongLine.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianLatticesGluedAlongLine.lean#L12-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedAlongLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LineGlue

theorem GlobalTheory.Mass.LineGlue.sup_span_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (B : Submodule R W) {y z : W} (hyz : y - z ∈ B) :
    B ⊔ Submodule.span R {y} = B ⊔ Submodule.span R {z} := by sorry
