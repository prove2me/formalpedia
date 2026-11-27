-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_exists_fixed_ne_zero
-- name    : GroundTheory.PAdicHodge.SemilinearResidue.exists_fixed_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:13.461886+00:00
-- url     : https://prove2.me/theorems/fb91abef-cd40-5d55-9410-b6c0d97acf0b
-- title:
--   Semilinear Residue: exists fixed ne zero
-- statement:
--   The Semilinear Residue construction uses the exists fixed ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L160-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L160-L209

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

theorem GroundTheory.PAdicHodge.SemilinearResidue.exists_fixed_ne_zero [IsAlgClosed k] [FiniteDimensional k V] (he : 0 < e)
    (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V)
    (hz : ∀ N, (⇑φ)^[N] z ≠ 0) : ∃ x, x ≠ 0 ∧ φ x = x := by sorry
