-- Prove2me | Theorems.Thm_GlobalTheory_CayleyInv_one_add_cayley_mul
-- name    : GlobalTheory.CayleyInv.one_add_cayley_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:59.992294+00:00
-- url     : https://prove2.me/theorems/636b212b-5785-41c0-8d00-0ef0c674a4b5
-- title:
--   Cayley Inv: one add cayley mul
-- statement:
--   The Cayley Inv construction uses the one add cayley mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CayleyTransformUnitarySkewInvolutive.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CayleyTransformUnitarySkewInvolutive.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.CayleyInv
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.CayleyInv.one_add_cayley_mul (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) (c : R)
    (hc : 2 * c = 1) : (1 + (1 - g) * (1 + g)⁻¹) * (c • (1 + g)) = 1 := by sorry
