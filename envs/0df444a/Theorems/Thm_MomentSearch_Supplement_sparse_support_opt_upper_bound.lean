-- Prove2me | Theorems.Thm_MomentSearch_Supplement_sparse_support_opt_upper_bound
-- name    : MomentSearch.Supplement.sparse_support_opt_upper_bound
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-21T00:52:43.76948+00:00
-- url     : https://prove2.me/theorems/91d5b55c-4452-4c3f-ae7c-f80e410c04f0
-- title:
--   Optimal search cost for sparse support
-- statement:
--   Let $p$ be a probability distribution on an ordered domain of size $n\ge2$. If at most $q\ge1$ positions have positive mass, then
--   $$0<\operatorname{OPT}(p)\le1+\log_2 q.$$
--   The strategy must identify every target, including positions of zero probability.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 6, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MomentSearch_OPT

theorem MomentSearch.Supplement.sparse_support_opt_upper_bound {n q : ℕ} (hn : 2 ≤ n) (hq : 0 < q) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (hs : (Function.support p).ncard ≤ q) :
    0 < MomentSearch.OPT p ∧ MomentSearch.OPT p ≤ 1 + Real.logb 2 q := by sorry
