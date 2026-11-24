-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_norm_sub_one_le_of_isPrimitiveRoot
-- name    : GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:33:58.347711+00:00
-- url     : https://prove2.me/theorems/668f837c-eb5c-4934-adb7-bd33f74415f5
-- title:
--   Cyc: norm sub one le of is Primitive Root
-- statement:
--   The Cyc construction uses the norm sub one le of is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPrimitiveRootPrimePowSubOnePadicComplex.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPrimitiveRootPrimePowSubOnePadicComplex.lean#L15-L32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc

theorem GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot {K : Type*} [NormedField K]
    [IsUltrametricDist K]
    {n : ℕ} (hn : n ≠ 0) {ζ μ : K} (hζ : IsPrimitiveRoot ζ n) (hμ : μ ^ n = 1) :
    ‖μ - 1‖ ≤ ‖ζ - 1‖ := by sorry
