-- Prove2me | Theorems.Thm_HamiltonDegree_chvatal
-- name    : HamiltonDegree.chvatal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:37:53.324733+00:00
-- url     : https://prove2.me/theorems/2b3a0cd1-3cf5-404a-8998-c6dbbe746599
-- title:
--   Hamilton Degree: chvatal
-- statement:
--   **Chvátal's theorem (1972), counting form.** A graph on `n ≥ 3` vertices is Hamiltonian if,
--   for every `i` with `1 ≤ i` and `2 i < n`, whenever at least `i` vertices have degree at most `i`,
--   at least `i + 1` vertices have degree at least `n - i`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/Solution.lean#L33-L37
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/Solution.lean#L33-L37

module
public import Mathlib
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa
public import Definitions.Def_ChvatalPosaHamiltonian_Solution
public import Theorems.Thm_ChvatalPosa_chvatal

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HamiltonDegree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem HamiltonDegree.chvatal (hn : 3 ≤ Fintype.card V)
    (h : ∀ i : ℕ, 1 ≤ i → 2 * i < Fintype.card V →
      i ≤ #{v | G.degree v ≤ i} → i + 1 ≤ #{v | Fintype.card V - i ≤ G.degree v}) :
    G.IsHamiltonian := by sorry
