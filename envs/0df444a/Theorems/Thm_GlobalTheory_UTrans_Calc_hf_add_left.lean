-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Calc_hf_add_left
-- name    : GlobalTheory.UTrans.Calc.hf_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:29.704851+00:00
-- url     : https://prove2.me/theorems/747552c8-713c-42da-848c-6408165673a7
-- title:
--   Calc: hf add left
-- statement:
--   The Calc construction uses the hf add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TransvectionIdentitiesUnitary.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TransvectionIdentitiesUnitary.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Calc
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

theorem GlobalTheory.UTrans.Calc.hf_add_left (x x' y : Fin n → R) : hf σ G (x + x') y = hf σ G x y + hf σ G x' y := by sorry
