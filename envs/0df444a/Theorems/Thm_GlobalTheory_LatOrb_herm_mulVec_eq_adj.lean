-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_herm_mulVec_eq_adj
-- name    : GlobalTheory.LatOrb.herm_mulVec_eq_adj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:58:36.771579+00:00
-- url     : https://prove2.me/theorems/bee6def0-5e7d-4c0d-adee-484130202515
-- title:
--   Lat Orb: herm mul Vec eq adj
-- statement:
--   The Lat Orb construction uses the herm mul Vec eq adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixImageAdjointMulEqOfSelfDualLattices.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixImageAdjointMulEqOfSelfDualLattices.lean#L8-L15

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixImageAdjointMulEqOfSelfDualLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrb

theorem GlobalTheory.LatOrb.herm_mulVec_eq_adj {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (x : Matrix (Fin n) (Fin n) K) (y m : Fin n → K) :
    herm σ y (x *ᵥ m) = herm σ ((x.map σ)ᵀ *ᵥ y) m := by sorry
