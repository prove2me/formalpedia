-- Prove2me | Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_equiv_of_stability
-- name    : GlobalTheory.Cmp.WachMonoidal.equiv_of_stability
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:26:10.36386+00:00
-- url     : https://prove2.me/theorems/37a12f9c-c587-49a4-a980-ffbdd1ab814e
-- title:
--   Wach Monoidal: equiv of stability
-- statement:
--   The Wach Monoidal construction uses the equiv of stability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitSumTensorDualOfWachMonoidal.lean#L446-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitSumTensorDualOfWachMonoidal.lean#L446-L449

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

theorem GlobalTheory.Cmp.WachMonoidal.equiv_of_stability (hT : CrystallineSubrepresentation.LocTensorCrys l P) (hD : CrystallineSubrepresentation.LocDualCrys l P) :
    UnitDualParts.UnitSumTensorDual l P AI H F ↔ TensorLatticeUnitPart.WachMonoidal l P AI H F := by sorry
