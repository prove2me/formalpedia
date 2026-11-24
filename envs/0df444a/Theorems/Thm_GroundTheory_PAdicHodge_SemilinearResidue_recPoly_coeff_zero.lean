-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_recPoly_coeff_zero
-- name    : GroundTheory.PAdicHodge.SemilinearResidue.recPoly_coeff_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:27.149634+00:00
-- url     : https://prove2.me/theorems/4603fb59-f8c1-4f7d-bda8-f50de1751fad
-- title:
--   Semilinear Residue: rec Poly coeff zero
-- statement:
--   The Semilinear Residue construction uses the rec Poly coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L45-L51

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

theorem GroundTheory.PAdicHodge.SemilinearResidue.recPoly_coeff_zero (c : ℕ → k) : ∀ i, (recPoly (p ^ e) c 0 i).coeff 0 = 0 := by sorry
