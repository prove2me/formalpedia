-- Prove2me | Theorems.Thm_LIPAlgorithm_corollary_2_12
-- name    : LIPAlgorithm.corollary_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:53:47.6692+00:00
-- url     : https://prove2.me/theorems/418e2dfe-99c7-4f90-a2dd-55482f1a663a
-- title:
--   Corollary 2.12 — $|\mathrm{Iso}(L_1,L_2)|\le B_{\mathrm{aut}}(n)\le O(n)^n$
-- statement:
--   Let $B_{\mathrm{aut}}(n)=\max\{2^{11}\cdot 11!,\ 2^n\cdot n!\}$. For all $n\ge1$ and all rank-$n$ lattices $L_1,L_2\subset\mathbb R^n$,
--
--   $$|\mathrm{Iso}(L_1,L_2)|\le B_{\mathrm{aut}}(n)\le O(n)^n .$$
--
--   This bounds the output of the all-isomorphisms problem, and the union bound over isomorphisms in the birthday argument.
--
--   Differences from the source:
--   - encoding: O(n)ⁿ → (C·n)ⁿ with one universal C; reason: footnote 2, p.2
--   - encoding: |Iso(L₁, L₂)| → Set.encard; reason: a bound on encard includes finiteness, whereas ncard would be 0 on an infinite set
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Corollary 2.12, p.13

import Mathlib
import Definitions.Def_LIPAlgorithm_minShell

namespace LIPAlgorithm

/-- **Corollary 2.12.** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256 61ee52aa…), Corollary 2.12,
p.13 (PDF p.16). With `Baut(n) = max{2¹¹·11!, 2ⁿ·n!}`: `|Iso(L₁, L₂)| ≤ Baut(n) ≤ O(n)ⁿ` for all rank-`n` lattices.

**Formalization Note.** `O(n)ⁿ` is `(C·n)ⁿ` with a universal `C` (footnote 2, p.2). The cardinality is `Set.encard`: a
finite bound on it says in particular that the set is finite, whereas `Set.ncard` would be `0` on an infinite set. -/
theorem corollary_2_12 :
    (∀ (n : ℕ) (L₁ L₂ : Submodule ℤ (E n)) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
        [DiscreteTopology L₂] [IsZLattice ℝ L₂], 1 ≤ n →
      (isoLat L₁ L₂).encard ≤ ((max (2 ^ 11 * Nat.factorial 11) (2 ^ n * Nat.factorial n) : ℕ) : ℕ∞)) ∧
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ((max (2 ^ 11 * Nat.factorial 11) (2 ^ n * Nat.factorial n) : ℕ) : ℝ) ≤ (C * n) ^ n := by sorry

end LIPAlgorithm
