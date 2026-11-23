-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Calc_tv_mulVec
-- name    : GlobalTheory.UTrans.Calc.tv_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:53.614426+00:00
-- url     : https://prove2.me/theorems/75933f9b-440b-4709-a266-891c26297df9
-- title:
--   Calc: tv mul Vec
-- statement:
--   The Calc construction uses the tv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TransvectionIdentitiesUnitary.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TransvectionIdentitiesUnitary.lean#L32-L40

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

theorem GlobalTheory.UTrans.Calc.tv_mulVec (x : Fin n → R) (t : R) (v : Fin n → R) :
    tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x := by sorry
