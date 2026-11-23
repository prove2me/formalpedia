-- Prove2me | Theorems.Thm_GlobalTheory_hermGenericMatrix_map_eval
-- name    : GlobalTheory.hermGenericMatrix_map_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:31.804917+00:00
-- url     : https://prove2.me/theorems/76a9d790-44b3-49bd-9569-9836da5d4031
-- title:
--   Global Theory: herm Generic Matrix map eval
-- statement:
--   The Global Theory construction uses the herm Generic Matrix map eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsHermitianDetNeZeroTwo.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsHermitianDetNeZeroTwo.lean#L11-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial Matrix

theorem GlobalTheory.hermGenericMatrix_map_eval {κ : Type} [Field κ] (n : ℕ) (e : κ)
    (u : Fin n × Fin n → κ) :
    (hermGenericMatrix n e).map (MvPolynomial.eval u) =
      Matrix.of fun i j => u (i, j) + u (j, i) + e * (u (i, j) - u (j, i)) := by sorry
