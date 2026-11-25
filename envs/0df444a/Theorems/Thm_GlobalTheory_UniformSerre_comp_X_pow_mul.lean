-- Prove2me | Theorems.Thm_GlobalTheory_UniformSerre_comp_X_pow_mul
-- name    : GlobalTheory.UniformSerre.comp_X_pow_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:49.983972+00:00
-- url     : https://prove2.me/theorems/ea244e32-9fc1-47c0-a7ed-ef2b4ead896f
-- title:
--   Uniform Serre: comp X pow mul
-- statement:
--   The Uniform Serre construction uses the comp X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L62-L66

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

theorem GlobalTheory.UniformSerre.comp_X_pow_mul (e : ℕ) (k : σ) (L : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) :
    comp e (X k ^ L * Q) = X k ^ L * comp e Q := by sorry
