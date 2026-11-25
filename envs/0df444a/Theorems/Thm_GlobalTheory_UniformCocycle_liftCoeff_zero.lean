-- Prove2me | Theorems.Thm_GlobalTheory_UniformCocycle_liftCoeff_zero
-- name    : GlobalTheory.UniformCocycle.liftCoeff_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:06.032531+00:00
-- url     : https://prove2.me/theorems/365836a6-0246-4bb1-b48c-e03293f3d168
-- title:
--   Uniform Cocycle: lift Coeff zero
-- statement:
--   The Uniform Cocycle construction uses the lift Coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L51-L54

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

theorem GlobalTheory.UniformCocycle.liftCoeff_zero (I : Ideal R) (e : ℕ) : liftCoeff I e 0 = 0 := by sorry
