-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_recPoly_coeff_one
-- name    : GroundTheory.PAdicHodge.SemilinearResidue.recPoly_coeff_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:43.592446+00:00
-- url     : https://prove2.me/theorems/7729ac48-dbd7-4aef-a8d0-d323097154bd
-- title:
--   Semilinear Residue: rec Poly coeff one
-- statement:
--   The Semilinear Residue construction uses the rec Poly coeff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L35-L43

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
variable {e : ℕ}

theorem GroundTheory.PAdicHodge.SemilinearResidue.recPoly_coeff_one (he : 0 < e) (c : ℕ → k) (ε : k) :
    ∀ i, (recPoly (p ^ e) c ε i).coeff 1 = 0 := by sorry
