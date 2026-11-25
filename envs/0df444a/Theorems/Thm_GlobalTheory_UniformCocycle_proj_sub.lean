-- Prove2me | Theorems.Thm_GlobalTheory_UniformCocycle_proj_sub
-- name    : GlobalTheory.UniformCocycle.proj_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:55:21.935247+00:00
-- url     : https://prove2.me/theorems/c0738bde-66e3-437a-b616-a92f1a52cf68
-- title:
--   Uniform Cocycle: proj sub
-- statement:
--   The Uniform Cocycle construction uses the proj sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L29-L31

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

theorem GlobalTheory.UniformCocycle.proj_sub (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P - Q) = proj I e P - proj I e Q := by sorry
