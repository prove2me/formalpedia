-- Prove2me | Theorems.Thm_GlobalTheory_UniformSerre_isHomogeneous_comp
-- name    : GlobalTheory.UniformSerre.isHomogeneous_comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:55:23.313015+00:00
-- url     : https://prove2.me/theorems/74bbcb84-ae99-444a-a7eb-642621a22fc9
-- title:
--   Uniform Serre: is Homogeneous comp
-- statement:
--   The Uniform Serre construction uses the is Homogeneous comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L72-L74

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

theorem GlobalTheory.UniformSerre.isHomogeneous_comp {e t : ℕ} {Q : MvPolynomial σ (reesAlgebra I)} (hQ : Q.IsHomogeneous t) :
    (comp e Q).IsHomogeneous t := by sorry
