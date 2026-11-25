-- Prove2me | Theorems.Thm_GlobalTheory_LatticeMinuscule_exists_mul_unit_iff
-- name    : GlobalTheory.LatticeMinuscule.exists_mul_unit_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:15.500334+00:00
-- url     : https://prove2.me/theorems/5bf04fab-3601-420c-abaf-e1459083b80b
-- title:
--   Lattice Minuscule: exists mul unit iff
-- statement:
--   The Lattice Minuscule construction uses the exists mul unit iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeElementaryDivisors.lean#L62-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeElementaryDivisors.lean#L62-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqMulDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeElementaryDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LatticeMinuscule
open Matrix
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}

theorem GlobalTheory.LatticeMinuscule.exists_mul_unit_iff (C : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin n) (Fin n) R)
    (hP : IsUnit P.det) (y : Fin n → K) :
    (∃ z : Fin n → R, y = C.mulVec (fun i => algebraMap R K (z i))) ↔
      ∃ z : Fin n → R,
        y = (C * P.map (algebraMap R K)).mulVec (fun i => algebraMap R K (z i)) := by sorry
