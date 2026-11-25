-- Prove2me | Theorems.Thm_GlobalTheory_isGradedMap_mulVecLin
-- name    : GlobalTheory.isGradedMap_mulVecLin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:33.916244+00:00
-- url     : https://prove2.me/theorems/7819d92d-7341-4a40-a6c3-ca84d959a6fb
-- title:
--   Global Theory: is Graded Map mul Vec Lin
-- statement:
--   The Global Theory construction uses the is Graded Map mul Vec Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsHomogeneousRangeMulVecLin.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsHomogeneousRangeMulVecLin.lean#L8-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsHomogeneousRangeMulVecLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory

theorem GlobalTheory.isGradedMap_mulVecLin {ι : Type} {R : Type*} [CommRing R] {κ μ : Type*} [Fintype μ]
    {d : κ → ℤ} {e : μ → ℤ} {Φ : Matrix κ μ (MvPolynomial ι R)}
    (h : ∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) :
    IsGradedMap (grFree ι R e) (grFree ι R d) Φ.mulVecLin := by sorry
