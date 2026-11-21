-- Prove2me | Theorems.Thm_MomentSearch_Supplement_dyadic_prefix_gram_factorization
-- name    : MomentSearch.Supplement.dyadic_prefix_gram_factorization
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-21T01:17:20.384473+00:00
-- url     : https://prove2.me/theorems/c6bda0d7-9e8c-4d33-be93-7422d2e9f7f7
-- title:
--   Factorization of prefix indicators from near-orthogonal labels
-- statement:
--   Let $h=1+\lceil\log_2 n\rceil$. Given $n$ labels in $\mathbb R^R$ whose inner products approximate the equality indicator within $\eta$, the prefix matrix $[j\le t]$ admits a factorization through $hR$ coordinates with entrywise additive error at most $h\eta$.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 27, p.35 (PDF p.37); construction preceding Theorem 27.

import Mathlib

theorem MomentSearch.Supplement.dyadic_prefix_gram_factorization {n R : ℕ} (hn : 2 ≤ n) {η : ℝ} (hη : 0 ≤ η)
    (g : Fin n → Fin R → ℝ)
    (hg : ∀ a b, |(∑ s, g a s * g b s) - (if a = b then 1 else 0)| ≤ η) :
    let h := Nat.clog 2 n + 1
    ∃ (U : Matrix (Fin n) (Fin (h*R)) ℝ) (V : Matrix (Fin (h*R)) (Fin n) ℝ),
      ∀ t j, |(U * V) t j - (if j ≤ t then 1 else 0)| ≤ (h:ℝ)*η := by sorry
