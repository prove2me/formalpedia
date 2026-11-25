-- Prove2me | Theorems.Thm_GlobalTheory_UniformSerre_coeff_lift
-- name    : GlobalTheory.UniformSerre.coeff_lift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:53:44.875641+00:00
-- url     : https://prove2.me/theorems/3f8346e4-9042-4393-a9fc-9fc5e71ce3d2
-- title:
--   Uniform Serre: coeff lift
-- statement:
--   The Uniform Serre construction uses the coeff lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L37-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSections
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

theorem GlobalTheory.UniformSerre.coeff_lift (e : ℕ) (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (lift I e P) = liftFun I e (coeff m P) := by sorry
