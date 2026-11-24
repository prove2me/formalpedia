-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_eval_map_eq_sum
-- name    : GlobalTheory.SimpleRoots.eval_map_eq_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:13:10.322215+00:00
-- url     : https://prove2.me/theorems/a3430e06-efe5-46ea-b4c6-c653e691e35e
-- title:
--   Simple Roots: eval map eq sum
-- statement:
--   The Simple Roots construction uses the eval map eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L9-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
open GlobalTheory GlobalTheory.SimpleRoots
variable {d : ℕ}

theorem GlobalTheory.SimpleRoots.eval_map_eq_sum (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x : Fin d → ℂ) (y : ℂ) :
    (p.map (MvPolynomial.eval x)).eval y
      = ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval x (p.coeff i) * y ^ i := by sorry
