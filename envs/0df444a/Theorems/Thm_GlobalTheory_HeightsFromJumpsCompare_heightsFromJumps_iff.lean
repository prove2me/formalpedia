-- Prove2me | Theorems.Thm_GlobalTheory_HeightsFromJumpsCompare_heightsFromJumps_iff
-- name    : GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:33:10.996803+00:00
-- url     : https://prove2.me/theorems/d03a6ecb-34e4-543a-b72d-16f2ef3d97e1
-- title:
--   Heights From Jumps Compare: heights From Jumps iff
-- statement:
--   The Heights From Jumps Compare construction uses the heights From Jumps iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeightsFromJumpsIff.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeightsFromJumpsIff.lean#L31-L35

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_PointRingCommRing
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_LocalRingStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeightsFromJumpsIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeightsFromJumpsCompare
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
open TensorProduct

theorem GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (AI : _root_.Formalism.BasicNotions.LocAinf l P)
    (H : _root_.Formalism.BasicNotions.LocHW l P) (F : _root_.Formalism.BasicNotions.LocFon l P AI H) (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H F C ↔
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure.HeightsFromJumps l P AI H F C := by sorry
