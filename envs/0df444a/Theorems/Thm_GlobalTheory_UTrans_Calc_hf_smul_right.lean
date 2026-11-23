-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Calc_hf_smul_right
-- name    : GlobalTheory.UTrans.Calc.hf_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:37.815049+00:00
-- url     : https://prove2.me/theorems/61d7857e-9fe7-46fc-8182-e3fac63a6839
-- title:
--   Calc: hf smul right
-- statement:
--   The Calc construction uses the hf smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TransvectionIdentitiesUnitary.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TransvectionIdentitiesUnitary.lean#L20-L23

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

theorem GlobalTheory.UTrans.Calc.hf_smul_right (c : R) (x y : Fin n → R) : hf σ G x (c • y) = σ c * hf σ G x y := by sorry
