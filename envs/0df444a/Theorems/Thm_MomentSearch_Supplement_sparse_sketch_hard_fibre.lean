-- Prove2me | Theorems.Thm_MomentSearch_Supplement_sparse_sketch_hard_fibre
-- name    : MomentSearch.Supplement.sparse_sketch_hard_fibre
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-21T00:52:10.134177+00:00
-- url     : https://prove2.me/theorems/4295137c-8d72-46e2-a85e-c4f5f477e317
-- title:
--   A short sketch has a hard fibre of sparse inputs
-- statement:
--   Let $n\ge2$ and $q\ge1$. A deterministic sketch of the probability simplex has at most $2^k$ messages, where $k\le(q/2)\log_2 n$. Then one message $x$ has the following property. For every ordered search tree $T$, there is a distribution $p$ with sketch $x$, supported on at most $q$ positions, such that
--   $$\operatorname{cost}_p(T)\ge\tfrac14\log_2 n.$$
--   The message is fixed before the tree is chosen.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 6, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MomentSearch_OPT

theorem MomentSearch.Supplement.sparse_sketch_hard_fibre {n q k : ℕ} (hn : 2 ≤ n) (hq : 0 < q)
    (X : Type) (σ : (Fin n → ℝ) → X)
    (hk : (k : ℝ) ≤ (q : ℝ) / 2 * Real.logb 2 n)
    (hfin : (σ '' stdSimplex ℝ (Fin n)).Finite)
    (hcard : (σ '' stdSimplex ℝ (Fin n)).ncard ≤ 2^k) :
    ∃ x ∈ σ '' stdSimplex ℝ (Fin n), ∀ T : MomentSearch.Strategy n,
      ∃ p ∈ stdSimplex ℝ (Fin n), σ p = x ∧
        (Function.support p).ncard ≤ q ∧ Real.logb 2 n / 4 ≤ MomentSearch.cost p T := by sorry
