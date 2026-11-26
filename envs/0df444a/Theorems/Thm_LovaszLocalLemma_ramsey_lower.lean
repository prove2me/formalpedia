-- Prove2me | Theorems.Thm_LovaszLocalLemma_ramsey_lower
-- name    : LovaszLocalLemma.ramsey_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:31:21.284164+00:00
-- url     : https://prove2.me/theorems/d396d71e-c0bb-4b05-a3c5-8bca03b6c7dd
-- title:
--   Lovasz Local Lemma: ramsey lower
-- statement:
--   **Spencer's Ramsey lower bound.** If `2 e (C(k,2) C(n,k-2) + 1) ≤ 2^C(k,2)`, some graph on
--   `n` vertices has no clique and no independent set of size `k`.
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/Solution.lean#L59-L62
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/Solution.lean#L59-L62

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Definitions.Def_LovaszLocalLemma_Solution
public import Theorems.Thm_LocalLemma_ramsey_lower

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LovaszLocalLemma

theorem LovaszLocalLemma.ramsey_lower {n k : ℕ}
    (h : 2 * Real.exp 1 * ((k.choose 2 * n.choose (k - 2) : ℕ) + 1) ≤ 2 ^ k.choose 2) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by sorry
