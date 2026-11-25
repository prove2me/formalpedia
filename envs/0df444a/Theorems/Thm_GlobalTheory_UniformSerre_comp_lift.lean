-- Prove2me | Theorems.Thm_GlobalTheory_UniformSerre_comp_lift
-- name    : GlobalTheory.UniformSerre.comp_lift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:53:38.597378+00:00
-- url     : https://prove2.me/theorems/ad36bb46-32df-4bac-9784-7031710d337e
-- title:
--   Uniform Serre: comp lift
-- statement:
--   The Uniform Serre construction uses the comp lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L46-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSections
import Theorems.Thm_GlobalTheory_IsGradedMap_comp

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

theorem GlobalTheory.UniformSerre.comp_lift (e e' : ℕ) (P : MvPolynomial σ R) (hP : ∀ m, coeff m P ∈ I ^ e) :
    comp e' (lift I e P) = if e' = e then P else 0 := by sorry
