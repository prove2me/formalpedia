-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_two_le_pow
-- name    : GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:48.80718+00:00
-- url     : https://prove2.me/theorems/5018a2ee-5045-4675-b070-66c3b98f3903
-- title:
--   Semilinear Residue: two le pow
-- statement:
--   The Semilinear Residue construction uses the two le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L28-L31

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
variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
omit [CharP k p]
include hp

theorem GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow {e : ℕ} (he : 0 < e) : 2 ≤ p ^ e := by sorry
