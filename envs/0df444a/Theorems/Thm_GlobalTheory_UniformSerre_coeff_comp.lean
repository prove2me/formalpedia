-- Prove2me | Theorems.Thm_GlobalTheory_UniformSerre_coeff_comp
-- name    : GlobalTheory.UniformSerre.coeff_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:10.965743+00:00
-- url     : https://prove2.me/theorems/b8869d82-db6f-4a8d-ac2d-e330a874530c
-- title:
--   Uniform Serre: coeff comp
-- statement:
--   The Uniform Serre construction uses the coeff comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L14-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSections
import Theorems.Thm_GlobalTheory_IsGradedMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.UniformSerre
variable {R : Type} [CommRing R] {I : Ideal R} {σ : Type}

theorem GlobalTheory.UniformSerre.coeff_comp (e : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    coeff m (comp e Q) = (coeff m Q).val.coeff e := by sorry
