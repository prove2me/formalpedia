-- Prove2me | Theorems.Thm_GlobalTheory_UniformCocycle_isHomogeneous_liftE
-- name    : GlobalTheory.UniformCocycle.isHomogeneous_liftE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:23.53464+00:00
-- url     : https://prove2.me/theorems/44ae56b1-8c1e-4fc6-a9c9-3db7ebfbc984
-- title:
--   Uniform Cocycle: is Homogeneous lift E
-- statement:
--   The Uniform Cocycle construction uses the is Homogeneous lift E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L78-L84

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

theorem GlobalTheory.UniformCocycle.isHomogeneous_liftE {I : Ideal R} {e t : ℕ} {F : MvPolynomial σ R}
    (hF : F.IsHomogeneous t) : (liftE I e F).IsHomogeneous t := by sorry
