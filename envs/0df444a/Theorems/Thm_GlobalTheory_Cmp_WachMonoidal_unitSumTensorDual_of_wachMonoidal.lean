-- Prove2me | Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_unitSumTensorDual_of_wachMonoidal
-- name    : GlobalTheory.Cmp.WachMonoidal.unitSumTensorDual_of_wachMonoidal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:57.35886+00:00
-- url     : https://prove2.me/theorems/6491a581-220c-57dc-ad5f-1cb9baa23593
-- title:
--   Wach Monoidal: unit Sum Tensor Dual of wach Monoidal
-- statement:
--   The Wach Monoidal construction uses the unit Sum Tensor Dual of wach Monoidal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitSumTensorDualOfWachMonoidal.lean#L442-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitSumTensorDualOfWachMonoidal.lean#L442-L444

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cmp GlobalTheory.Cmp.WachMonoidal
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke
variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)

theorem GlobalTheory.Cmp.WachMonoidal.unitSumTensorDual_of_wachMonoidal (h : TensorLatticeUnitPart.WachMonoidal l P AI H F) :
    UnitDualParts.UnitSumTensorDual l P AI H F := by sorry
