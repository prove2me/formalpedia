-- Prove2me | Theorems.Thm_GlobalTheory_Hadamard_norm_det_le_prod_col
-- name    : GlobalTheory.Hadamard.norm_det_le_prod_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:48.396124+00:00
-- url     : https://prove2.me/theorems/743e86d7-4e64-47c0-a643-473f4541fdda
-- title:
--   Hadamard: norm det le prod col
-- statement:
--   The Hadamard construction uses the norm det le prod col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L29-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
open scoped InnerProductSpace ComplexOrder
open GlobalTheory GlobalTheory.Hadamard
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem GlobalTheory.Hadamard.norm_det_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ j, √(∑ i, ‖A i j‖ ^ 2) := by sorry
