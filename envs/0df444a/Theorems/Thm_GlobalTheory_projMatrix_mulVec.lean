-- Prove2me | Theorems.Thm_GlobalTheory_projMatrix_mulVec
-- name    : GlobalTheory.projMatrix_mulVec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:46.045803+00:00
-- url     : https://prove2.me/theorems/d9d39e9c-8be3-4ad7-a5dc-16cd1298cb11
-- title:
--   Global Theory: proj Matrix mul Vec
-- statement:
--   The Global Theory construction uses the proj Matrix mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMatricesOfProjectiveComplex.lean#L54-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMatricesOfProjectiveComplex.lean#L54-L69

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

theorem GlobalTheory.projMatrix_mulVec {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) (x : R' ⊗[R] (Fin a → R)) :
    ((LinearMap.toMatrix' f).map (algebraMap R R')).mulVec
        (TensorProduct.piScalarRight R R' R' (Fin a) x) =
      TensorProduct.piScalarRight R R' R' (Fin b) (f.baseChange R' x) := by sorry
