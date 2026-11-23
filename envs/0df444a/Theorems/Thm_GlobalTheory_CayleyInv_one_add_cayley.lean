-- Prove2me | Theorems.Thm_GlobalTheory_CayleyInv_one_add_cayley
-- name    : GlobalTheory.CayleyInv.one_add_cayley
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:46.924922+00:00
-- url     : https://prove2.me/theorems/9fb8834e-2676-4ccf-8681-1b8b597081de
-- title:
--   Cayley Inv: one add cayley
-- statement:
--   The Cayley Inv construction uses the one add cayley property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CayleyTransformUnitarySkewInvolutive.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CayleyTransformUnitarySkewInvolutive.lean#L23-L30

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

theorem GlobalTheory.CayleyInv.one_add_cayley (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) :
    1 + (1 - g) * (1 + g)⁻¹ = (2 : R) • (1 + g)⁻¹ := by sorry
