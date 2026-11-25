-- Prove2me | Theorems.Thm_GlobalTheory_projMatrix_sum
-- name    : GlobalTheory.projMatrix_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:07.94774+00:00
-- url     : https://prove2.me/theorems/b28e26fc-ba77-47b7-8458-74221d92c7de
-- title:
--   Global Theory: proj Matrix sum
-- statement:
--   The Global Theory construction uses the proj Matrix sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMatricesOfProjectiveComplex.lean#L71-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMatricesOfProjectiveComplex.lean#L71-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMatricesOfProjectiveComplex
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

theorem GlobalTheory.projMatrix_sum {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    {a : ℕ} {P : Type} [AddCommGroup P] [Module R P] (p : (Fin a → R) →ₗ[R] P)
    (x : R' ⊗[R] (Fin a → R)) :
    ∑ k, TensorProduct.piScalarRight R R' R' (Fin a) x k ⊗ₜ[R] p (Pi.single k 1) =
      p.baseChange R' x := by sorry
