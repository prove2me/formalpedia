-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_exists_sub_mul_mem
-- name    : GlobalTheory.CoeffSubring.exists_sub_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:02.385797+00:00
-- url     : https://prove2.me/theorems/1f4ed7ec-7e35-460b-b518-aaeac4c99521
-- title:
--   Coeff Subring: exists sub mul mem
-- statement:
--   The Coeff Subring construction uses the exists sub mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L128-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L128-L200

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}

theorem GlobalTheory.CoeffSubring.exists_sub_mul_mem (hp : p.Prime) (h0 : (p : S) ∈ maximalIdeal S)
    (hL : Set.InjOn (residue S) L)
    (hB : ∀ (Q : Type) [CommRing Q] (f : ResidueField S →+* Q) (g : ResidueField S → Q),
      (∀ b ∈ residue S '' L, g b ^ p = f b) →
      ∃ σ : ResidueField S →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ residue S '' L, σ b = g b)
    (hs : ∀ n s, ∃ t ∈ level p L n, s - t ∈ maximalIdeal S) (n : ℕ) {a : S}
    (ha : a ∈ level p L n) (ha' : a ∈ maximalIdeal S) :
    ∃ t ∈ level p L n, a - p * t ∈ maximalIdeal S ^ (n + 1) := by sorry
