-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_near_one
-- name    : GlobalTheory.MinorInt.near_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:00.878802+00:00
-- url     : https://prove2.me/theorems/298d478b-3a37-456c-8cd1-3ebb91251005
-- title:
--   Minor Int: near one
-- statement:
--   The Minor Int construction uses the near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L42-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L42-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt

theorem GlobalTheory.MinorInt.near_one (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ G : Matrix ι ι ℂ, (∀ i j, ‖(G - 1) i j‖ < δ) →
      1 / 2 ≤ ‖G.det‖ ∧ 1 / 2 ≤ ‖(1 - (2 : ℂ) • G).det‖ ∧
        ∀ t : ι → ℂ, (∑ i, ‖t i‖ ^ 2) / 2 ≤ (star t ⬝ᵥ G *ᵥ t).re := by sorry
