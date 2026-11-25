-- Prove2me | Theorems.Thm_GlobalTheory_DeligneSerre_eq_top_of_isUnit_det
-- name    : GlobalTheory.DeligneSerre.eq_top_of_isUnit_det
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:51:48.309808+00:00
-- url     : https://prove2.me/theorems/5f528b85-3778-4b20-baa9-d48595f1242f
-- title:
--   Deligne Serre: eq top of is Unit det
-- statement:
--   The Deligne Serre construction uses the eq top of is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntegralHeckeEigensystemDeligneSerre.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntegralHeckeEigensystemDeligneSerre.lean#L11-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixExistsCommonEigenvectorMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteJointEigensystemsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatricesIntertwiningOfSemilinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralHeckeEigensystemDeligneSerre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.DeligneSerre

theorem GlobalTheory.DeligneSerre.eq_top_of_isUnit_det (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ)
    (σ : R →ₐ[O] Matrix (Fin n) (Fin n) O) (m : Ideal R) (hker : ∀ p, σ p = 0 → p ∈ m) (p : R)
    (hp : p ∈ m) (hu : IsUnit (σ p).det) : m = ⊤ := by sorry
