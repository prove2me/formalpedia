-- Prove2me | Theorems.Thm_GlobalTheory_Mem_InvDer_hasDerivAt_inv_det_and_inv
-- name    : GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:23:16.608787+00:00
-- url     : https://prove2.me/theorems/39f10c50-68dd-4627-a71c-f102b92052c8
-- title:
--   Inv Der: has Deriv At inv det and inv
-- statement:
--   The Inv Der construction uses the has Deriv At inv det and inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HasDerivAtInvDetAndInvAtIdentity.lean#L8-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HasDerivAtInvDetAndInvAtIdentity.lean#L8-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HasDerivAtInvDetAndInvAtIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.InvDer

theorem GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (M' : Matrix (Fin n) (Fin n) ℂ) (h0 : M 0 = 1)
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0) :
    HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 ∧
      ∀ i j, HasDerivAt (fun t => (M t)⁻¹ i j) (-M' i j) 0 := by sorry
