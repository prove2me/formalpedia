-- Prove2me | Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_mul
-- name    : GlobalTheory.Mass.DiscOrder.idxN_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:07.398043+00:00
-- url     : https://prove2.me/theorems/23e4d3e6-46c9-4fa4-a32e-5e754d792045
-- title:
--   Disc Order: idx N mul
-- statement:
--   The Disc Order construction uses the idx N mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLatticeDiscriminantOrderNeZeroUnimodula.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLatticeDiscriminantOrderNeZeroUnimodula.lean#L21-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem GlobalTheory.Mass.DiscOrder.idxN_mul {A B C : Submodule R W} (h1 : A ≤ B) (h2 : B ≤ C) :
    idxN B A * idxN C B = idxN C A := by sorry
