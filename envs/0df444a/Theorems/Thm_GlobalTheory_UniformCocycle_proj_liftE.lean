-- Prove2me | Theorems.Thm_GlobalTheory_UniformCocycle_proj_liftE
-- name    : GlobalTheory.UniformCocycle.proj_liftE
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:15.590454+00:00
-- url     : https://prove2.me/theorems/65f903ab-9792-49cf-a540-7f615e537a0c
-- title:
--   Uniform Cocycle: proj lift E
-- statement:
--   The Uniform Cocycle construction uses the proj lift E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L69-L76

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

theorem GlobalTheory.UniformCocycle.proj_liftE {I : Ideal R} {e : ℕ} {F : MvPolynomial σ R} (h : ∀ m, coeff m F ∈ I ^ e)
    (e' : ℕ) : proj I e' (liftE I e F) = if e' = e then F else 0 := by sorry
