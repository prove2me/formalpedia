-- Prove2me | Theorems.Thm_GlobalTheory_LatticeMinuscule_map_mulVec_algebraMap
-- name    : GlobalTheory.LatticeMinuscule.map_mulVec_algebraMap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:59:49.066312+00:00
-- url     : https://prove2.me/theorems/dd721910-a83d-4bb1-8c44-eab503fb6c7c
-- title:
--   Lattice Minuscule: map mul Vec algebra Map
-- statement:
--   The Lattice Minuscule construction uses the map mul Vec algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeElementaryDivisors.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeElementaryDivisors.lean#L11-L16

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

theorem GlobalTheory.LatticeMinuscule.map_mulVec_algebraMap (M : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    (M.map (algebraMap R K)).mulVec (fun i => algebraMap R K (z i))
      = fun i => algebraMap R K (M.mulVec z i) := by sorry
