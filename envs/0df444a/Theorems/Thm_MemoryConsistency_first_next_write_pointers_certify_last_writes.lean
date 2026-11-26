-- Prove2me | Theorems.Thm_MemoryConsistency_first_next_write_pointers_certify_last_writes
-- name    : MemoryConsistency.first_next_write_pointers_certify_last_writes
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T19:12:22.156284+00:00
-- url     : https://prove2.me/theorems/995e3e6f-0b15-5f46-b4a7-e0cf7ac5b927
-- title:
--   Local certificates for previous writes
-- statement:
--   Consider a finite chronology of memory records. Every record has an address and a flag that says whether it writes. Each record names a claimed previous write to that same address, or claims there is none. Supply two extra tables, one naming the first write at each address and one naming the next write following each store. At a query record with no claimed previous write, the first-write pointer must be absent or at least the current time. At a query with a claimed previous write, that record must be a strictly earlier write at the same address, and its next-write pointer must be absent or at least the current time. If the current record writes, the corresponding first-write or next-write pointer must point to the current record. These local requirements can be met exactly when every claimed previous write is the true last strictly earlier write to the query address.
-- source:
--   Related memory-consistency constructions use timestamps or a second execution trace ordered by address. See Blum, Evans, Gemmell, Kannan, and Naor, Checking the Correctness of Memories, Section 4, https://www.cs.ubc.ca/~will/papers/memcheck.pdf, and Ben-Sasson, Chiesa, Genkin, Tromer, and Virza, SNARKs for C, Section 2.4, https://faculty.cc.gatech.edu/~genkin/papers/csnark-20131007.pdf. This theorem formalizes a direct pointer criterion for an arbitrary finite chronology.

import Mathlib

theorem MemoryConsistency.first_next_write_pointers_certify_last_writes
    {A : Type} (address : ℕ → A) (stores : ℕ → Bool) (previous : ℕ → Option ℕ) (H : ℕ) :
    let writesAt (a : A) (i : ℕ) := stores i = true ∧ address i = a
    let notBefore (t : ℕ) (p : Option ℕ) : Prop :=
      match p with
      | none => True
      | some r => t ≤ r
    (∃ next : ℕ → Option ℕ, ∃ first : A → Option ℕ, ∀ t < H,
      match previous t with
      | none => notBefore t (first (address t)) ∧
          (stores t = true → first (address t) = some t)
      | some s => s < t ∧ writesAt (address t) s ∧ notBefore t (next s) ∧
          (stores t = true → next s = some t)) ↔
    ∀ t < H, match previous t with
    | none => ∀ r < t, ¬ writesAt (address t) r
    | some s => s < t ∧ writesAt (address t) s ∧
        ∀ r, s < r → r < t → ¬ writesAt (address t) r := by sorry
