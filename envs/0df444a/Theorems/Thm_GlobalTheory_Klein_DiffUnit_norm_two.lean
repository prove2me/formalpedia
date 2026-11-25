-- Prove2me | Theorems.Thm_GlobalTheory_Klein_DiffUnit_norm_two
-- name    : GlobalTheory.Klein.DiffUnit.norm_two
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:20.983936+00:00
-- url     : https://prove2.me/theorems/e853e2b4-3bfb-5338-b65b-b0dffc664936
-- title:
--   Diff Unit: norm two
-- statement:
--   The Diff Unit construction uses the norm two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormWeierstrassPSubEqOne.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormWeierstrassPSubEqOne.lean#L23-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormWeierstrassPSubEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein GlobalTheory.Klein.DiffUnit
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.Klein.DiffUnit.norm_two (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by sorry
