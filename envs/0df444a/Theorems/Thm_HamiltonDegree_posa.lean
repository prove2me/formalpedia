-- Prove2me | Theorems.Thm_HamiltonDegree_posa
-- name    : HamiltonDegree.posa
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:38:52.531321+00:00
-- url     : https://prove2.me/theorems/ecb9731d-aeea-43d9-90c7-f24adef67e66
-- title:
--   Hamilton Degree: posa
-- statement:
--   **Pósa's theorem (1962).** A graph on `n ≥ 3` vertices is Hamiltonian if, for every `k` with
--   `1 ≤ k` and `2 k < n - 1`, fewer than `k` vertices have degree at most `k`, and, when `n` is odd,
--   at most `(n - 1) / 2` vertices have degree at most `(n - 1) / 2`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/Solution.lean#L42-L47
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/Solution.lean#L42-L47

module
public import Mathlib
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa
public import Definitions.Def_ChvatalPosaHamiltonian_Solution
public import Theorems.Thm_ChvatalPosa_posa

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HamiltonDegree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem HamiltonDegree.posa (hn : 3 ≤ Fintype.card V)
    (h₁ : ∀ k : ℕ, 1 ≤ k → 2 * k < Fintype.card V - 1 → #{v | G.degree v ≤ k} < k)
    (h₂ : Odd (Fintype.card V) →
      #{v | G.degree v ≤ (Fintype.card V - 1) / 2} ≤ (Fintype.card V - 1) / 2) :
    G.IsHamiltonian := by sorry
