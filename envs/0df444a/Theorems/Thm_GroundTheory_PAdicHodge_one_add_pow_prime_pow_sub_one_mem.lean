-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_one_add_pow_prime_pow_sub_one_mem
-- name    : GroundTheory.PAdicHodge.one_add_pow_prime_pow_sub_one_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:50.589889+00:00
-- url     : https://prove2.me/theorems/3a01b12b-11d7-4f70-9e43-c59a03f6e90a
-- title:
--   PAdic Hodge: one add pow prime pow sub one mem
-- statement:
--   The PAdic Hodge construction uses the one add pow prime pow sub one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L15-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L15-L35

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Ideal WittVector IsLocalRing
variable {A : Type*} [CommRing A]

theorem GroundTheory.PAdicHodge.one_add_pow_prime_pow_sub_one_mem {p : ℕ} (hp : p.Prime) (y : A) (N r k : ℕ)
    (hk : k ≤ p ^ r) :
    (1 + y) ^ (p ^ N) - 1 ∈ span {(p : A) ^ (N - r)} ⊔ span {y ^ k} := by sorry
