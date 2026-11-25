-- Prove2me | Theorems.Thm_GlobalTheory_xProd_smul_bijective_of
-- name    : GlobalTheory.xProd_smul_bijective_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:51:29.102921+00:00
-- url     : https://prove2.me/theorems/1ce8ea91-aba9-4109-bb5f-f0dd1bc2f83c
-- title:
--   Global Theory: x Prod smul bijective of
-- statement:
--   The Global Theory construction uses the x Prod smul bijective of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsHomLocBijectiveGrSum.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsHomLocBijectiveGrSum.lean#L34-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsHomLocBijectiveGrSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type} [CommRing R]

theorem GlobalTheory.xProd_smul_bijective_of {N : Type} [AddCommGroup N] [Module (MvPolynomial ι R) N]
    (s : Finset ι) (h : ∀ i ∈ s, Function.Bijective fun m : N => (X i : MvPolynomial ι R) • m) :
    Function.Bijective fun m : N => xProd R s • m := by sorry
