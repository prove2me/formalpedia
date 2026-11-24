-- Prove2me | Theorems.Thm_GlobalTheory_CayleyInv_map_one_sub
-- name    : GlobalTheory.CayleyInv.map_one_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:12.91408+00:00
-- url     : https://prove2.me/theorems/8ab7e02b-f720-4ae9-93e3-6e17ae60afd4
-- title:
--   Cayley Inv: map one sub
-- statement:
--   The Cayley Inv construction uses the map one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CayleyTransformUnitarySkewInvolutive.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CayleyTransformUnitarySkewInvolutive.lean#L19-L21

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

theorem GlobalTheory.CayleyInv.map_one_sub (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    (1 - M).map σ = 1 - M.map σ := by sorry
