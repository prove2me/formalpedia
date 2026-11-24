-- Prove2me | Theorems.Thm_GlobalTheory_Hadamard_re_det_gram_sum_smul
-- name    : GlobalTheory.Hadamard.re_det_gram_sum_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:59.995683+00:00
-- url     : https://prove2.me/theorems/4064dff4-3db2-413c-99c5-e30d552c2dea
-- title:
--   Hadamard: re det gram sum smul
-- statement:
--   The Hadamard construction uses the re det gram sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L69-L75

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

theorem GlobalTheory.Hadamard.re_det_gram_sum_smul (e : ι → E) (m : Matrix ι ι 𝕜) :
    RCLike.re (gram 𝕜 (fun j => ∑ i, m i j • e i)).det
      = ‖m.det‖ ^ 2 * RCLike.re (gram 𝕜 e).det := by sorry
