-- Prove2me | Theorems.Thm_GlobalTheory_ResidueCharacterDense_isOpen_ball
-- name    : GlobalTheory.ResidueCharacterDense.isOpen_ball
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:28:34.24623+00:00
-- url     : https://prove2.me/theorems/14e0813e-91a3-5380-b569-628f479d3ddb
-- title:
--   Residue Character Dense: is Open ball
-- statement:
--   The Residue Character Dense construction uses the is Open ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L10-L17

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense

theorem GlobalTheory.ResidueCharacterDense.isOpen_ball (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : IsOpen {z : K | valuation K z < 1} := by sorry
