-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_solve_of_root
-- name    : GroundTheory.PAdicHodge.SemilinearResidue.solve_of_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:13.948382+00:00
-- url     : https://prove2.me/theorems/e063774e-6af3-4487-9b23-7618f8920e3d
-- title:
--   Semilinear Residue: solve of root
-- statement:
--   The Semilinear Residue construction uses the solve of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L124-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L124-L138

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module Finset
open GroundTheory.PAdicHodge.SemilinearResidue
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}
omit hp [CharP k p]

theorem GroundTheory.PAdicHodge.SemilinearResidue.solve_of_root (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V) (n : ℕ)
    (c : ℕ → k) (hrel : (⇑φ)^[n + 1] z = ∑ i ∈ range (n + 1), c i • (⇑φ)^[i] z) (ε y : k)
    (hy : (recPoly (p ^ e) c ε n).eval y = y) :
    φ (∑ i ∈ range (n + 1), (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) =
      (∑ i ∈ range (n + 1), (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) + ε • z := by sorry
