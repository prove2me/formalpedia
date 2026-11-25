-- Prove2me | Theorems.Thm_GlobalTheory_UniformSerre_comp_sub
-- name    : GlobalTheory.UniformSerre.comp_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:55:24.775043+00:00
-- url     : https://prove2.me/theorems/b12552b5-14c1-4e89-a9f9-9e28abe7f6a4
-- title:
--   Uniform Serre: comp sub
-- statement:
--   The Uniform Serre construction uses the comp sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L57-L60

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

theorem GlobalTheory.UniformSerre.comp_sub (e : ℕ) (Q₁ Q₂ : MvPolynomial σ (reesAlgebra I)) :
    comp e (Q₁ - Q₂) = comp e Q₁ - comp e Q₂ := by sorry
