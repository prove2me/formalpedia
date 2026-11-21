-- Prove2me | Theorems.Thm_MomentSearch_Supplement_smoothed_step_certificate
-- name    : MomentSearch.Supplement.smoothed_step_certificate
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-21T01:14:32.349748+00:00
-- url     : https://prove2.me/theorems/e40a8c9b-10da-4ed5-8f66-f9eb7de8fa94
-- title:
--   One-sided smoothed polynomial step on a finite grid
-- statement:
--   Let $n\ge3$ and $k\ge16$ be integers, and let $M,W$ be nonnegative integers with
--   $$96\frac nk\log_2 n\le W,\qquad 2W\le n-1,\qquad M+W\le n-1.$$
--   There exists a real polynomial $q$ of degree at most $k$ such that, at every grid point $t\in\{0,\ldots,n-1\}$,
--   $$0\le q(t)\le1+n^{-2},$$
--   and moreover
--   $$t\le M\implies q(t)\ge1,\qquad t\ge M+W\implies q(t)\le n^{-2}.$$
--   This is the one-sided smoothed-step certificate underlying Theorem 18. It is independent of distributions and of the moment constraints.
--
--   The source states the bounds on real intervals and uses the weaker width threshold $96(n/k)\ln n$. Here only the integer grid is retained and the threshold uses $\log_2 n$, which is at least $\ln n$. Thus this is a specialization of the source lemma. The intended construction squares a shifted Chebyshev polynomial, integrates and normalizes the resulting nonnegative bump, and rescales to majorize the prefix indicator. The certificate's construction remains to be formalized.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559, held version used by this mission; one-sided smoothed-step lemma (label lem:cert) and its proof in the appendix on moment recovery, immediately before Theorem 18. Grid restriction with the stronger base-2-log width hypothesis.

import Mathlib

namespace MomentSearch.Supplement

theorem smoothed_step_certificate (n k M W : ℕ) (hn : 3 ≤ n) (hk : 16 ≤ k)
    (hW : 96 * ((n : ℝ) / k) * Real.logb 2 n ≤ (W : ℝ))
    (hhalf : 2 * W ≤ n - 1) (hMW : M + W ≤ n - 1) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ k ∧
      (∀ t : Fin n, 0 ≤ q.eval (t.val : ℝ)) ∧
      (∀ t : Fin n, t.val ≤ M → 1 ≤ q.eval (t.val : ℝ)) ∧
      (∀ t : Fin n, q.eval (t.val : ℝ) ≤ 1 + 1 / (n : ℝ)^2) ∧
      (∀ t : Fin n, M + W ≤ t.val → q.eval (t.val : ℝ) ≤ 1 / (n : ℝ)^2) := by sorry

end MomentSearch.Supplement
