-- Prove2me | Theorems.Thm_GlobalTheory_UniformCocycle_proj_add
-- name    : GlobalTheory.UniformCocycle.proj_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:53:37.247036+00:00
-- url     : https://prove2.me/theorems/b91bb09b-ec53-49a6-8859-8e0b2fbf9433
-- title:
--   Uniform Cocycle: proj add
-- statement:
--   The Uniform Cocycle construction uses the proj add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean#L25-L27

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

theorem GlobalTheory.UniformCocycle.proj_add (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P + Q) = proj I e P + proj I e Q := by sorry
