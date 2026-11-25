-- Prove2me | Theorems.Thm_GlobalTheory_exists_witnesses_of_formallySmooth_quotient
-- name    : GlobalTheory.exists_witnesses_of_formallySmooth_quotient
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:39.682117+00:00
-- url     : https://prove2.me/theorems/e2196225-3321-4848-8ea8-02a8e38c7499
-- title:
--   Global Theory: exists witnesses of formally Smooth quotient
-- statement:
--   The Global Theory construction uses the exists witnesses of formally Smooth quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsWitnessesOfFormallySmoothQuotient.lean#L25-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsWitnessesOfFormallySmoothQuotient.lean#L25-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsWitnessesOfFormallySmoothQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory

theorem GlobalTheory.exists_witnesses_of_formallySmooth_quotient :
    ∀ (ι : Type) [Fintype ι] (R : Type) [CommRing R] (r : ℕ) (g : Fin r → MvPolynomial ι R), Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) → ∃ (a : ι → Fin r → MvPolynomial ι R) (b : Fin r → Fin r → Fin r → MvPolynomial ι R), ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l) := by sorry
