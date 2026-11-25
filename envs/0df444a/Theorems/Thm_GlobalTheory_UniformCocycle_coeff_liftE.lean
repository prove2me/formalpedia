-- Prove2me | Theorems.Thm_GlobalTheory_UniformCocycle_coeff_liftE
-- name    : GlobalTheory.UniformCocycle.coeff_liftE
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:34.814807+00:00
-- url     : https://prove2.me/theorems/b2eb7b85-2079-4f38-8e18-8ee317aa9373
-- title:
--   Uniform Cocycle: coeff lift E
-- statement:
--   The Uniform Cocycle construction uses the coeff lift E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L60-L67

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

theorem GlobalTheory.UniformCocycle.coeff_liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (liftE I e F) = liftCoeff I e (coeff m F) := by sorry
