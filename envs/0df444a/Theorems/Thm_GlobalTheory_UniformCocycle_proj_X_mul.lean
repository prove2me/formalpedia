-- Prove2me | Theorems.Thm_GlobalTheory_UniformCocycle_proj_X_mul
-- name    : GlobalTheory.UniformCocycle.proj_X_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:10.182721+00:00
-- url     : https://prove2.me/theorems/6c4a5fe5-5654-4e23-83da-fe8502051cde
-- title:
--   Uniform Cocycle: proj X mul
-- statement:
--   The Uniform Cocycle construction uses the proj X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L33-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdeaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreVanishingCechCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.UniformCocycle
variable {R : Type} [CommRing R] {σ : Type}

theorem GlobalTheory.UniformCocycle.proj_X_mul (I : Ideal R) (e : ℕ) (i : σ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i * P) = X i * proj I e P := by sorry
