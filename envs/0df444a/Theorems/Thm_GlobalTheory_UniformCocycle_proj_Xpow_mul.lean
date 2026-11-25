-- Prove2me | Theorems.Thm_GlobalTheory_UniformCocycle_proj_Xpow_mul
-- name    : GlobalTheory.UniformCocycle.proj_Xpow_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:05.853079+00:00
-- url     : https://prove2.me/theorems/53097fb6-d5cc-4a5f-b8c0-35f8a26e878c
-- title:
--   Uniform Cocycle: proj Xpow mul
-- statement:
--   The Uniform Cocycle construction uses the proj Xpow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L40-L44

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

theorem GlobalTheory.UniformCocycle.proj_Xpow_mul (I : Ideal R) (e : ℕ) (i : σ) (k : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i ^ k * P) = X i ^ k * proj I e P := by sorry
