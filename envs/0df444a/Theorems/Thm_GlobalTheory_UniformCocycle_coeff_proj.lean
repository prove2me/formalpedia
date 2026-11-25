-- Prove2me | Theorems.Thm_GlobalTheory_UniformCocycle_coeff_proj
-- name    : GlobalTheory.UniformCocycle.coeff_proj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:18.574712+00:00
-- url     : https://prove2.me/theorems/a1d1119d-a0c7-4d1e-9ceb-f9184116cb3f
-- title:
--   Uniform Cocycle: coeff proj
-- statement:
--   The Uniform Cocycle construction uses the coeff proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L16-L23

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

theorem GlobalTheory.UniformCocycle.coeff_proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    coeff m (proj I e P) = ((coeff m P : reesAlgebra I) : Polynomial R).coeff e := by sorry
