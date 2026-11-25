-- Prove2me | Theorems.Thm_GlobalTheory_UnifCorr_mem_of_coeff_mem
-- name    : GlobalTheory.UnifCorr.mem_of_coeff_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:09:10.097673+00:00
-- url     : https://prove2.me/theorems/2a9cbdea-4a83-481e-9fd4-771322f0eff6
-- title:
--   Unif Corr: mem of coeff mem
-- statement:
--   The Unif Corr construction uses the mem of coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousCorrectionNextLevel.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousCorrectionNextLevel.lean#L18-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousCorrectionNextLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.UnifCorr
variable {R : Type} [CommRing R] {σ : Type}

theorem GlobalTheory.UnifCorr.mem_of_coeff_mem (I : Ideal R) (K : Ideal (MvPolynomial σ R))
    (hC : ∀ a ∈ I, C a ∈ K) (G : MvPolynomial σ R) (h : ∀ m, coeff m G ∈ I) : G ∈ K := by sorry
