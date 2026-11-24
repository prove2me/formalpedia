-- Prove2me | Theorems.Thm_GlobalTheory_TvAdjust_tv_mul_mulVec
-- name    : GlobalTheory.TvAdjust.tv_mul_mulVec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:01.864084+00:00
-- url     : https://prove2.me/theorems/7289c6b7-eebf-4730-b3cf-9485cdf87c2a
-- title:
--   Tv Adjust: tv mul mul Vec
-- statement:
--   The Tv Adjust construction uses the tv mul mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTraceZeroAdjustmentOfHermitianLattice.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTraceZeroAdjustmentOfHermitianLattice.lean#L53-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMulVecMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTraceZeroAdjustmentOfHermitianLattice
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
open GlobalTheory GlobalTheory.TvAdjust

theorem GlobalTheory.TvAdjust.tv_mul_mulVec {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
    (x v : Fin n → R) (t : R) (q : ℤ) :
    tv σ G x (q * t) *ᵥ v = v + q • ((tv σ G x t - 1) *ᵥ v) := by sorry
