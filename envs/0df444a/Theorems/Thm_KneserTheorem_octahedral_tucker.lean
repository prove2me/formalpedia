-- Prove2me | Theorems.Thm_KneserTheorem_octahedral_tucker
-- name    : KneserTheorem.octahedral_tucker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:04:35.426371+00:00
-- url     : https://prove2.me/theorems/55437417-7660-4b3b-a926-e05b09c0c8b8
-- title:
--   Kneser Theorem: octahedral tucker
-- statement:
--   **The octahedral Tucker lemma.** An antipodal labelling of the nonzero sign vectors of length
--   `n` by nonzero integers in `[-m, m]` with `m < n` has a complementary pair `x ≼ y`.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/Solution.lean#L37-L41
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/Solution.lean#L37-L41

module
public import Mathlib
public import Definitions.Def_KneserLib_Kneser
public import Definitions.Def_KneserLovasz_Solution
public import Theorems.Thm_KneserColouring_octahedral_tucker

set_option autoImplicit true
@[expose] public section
public section
open KneserTheorem

theorem KneserTheorem.octahedral_tucker {n m : ℕ} (lab : (Fin n → SignType) → ℤ)
    (hlab : ∀ x, x ≠ 0 → lab x ≠ 0 ∧ |lab x| ≤ m)
    (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x) (hm : m < n) :
    ∃ x y : Fin n → SignType, x ≠ 0 ∧ (∀ i, x i ≠ 0 → x i = y i) ∧ lab x = -lab y := by sorry
