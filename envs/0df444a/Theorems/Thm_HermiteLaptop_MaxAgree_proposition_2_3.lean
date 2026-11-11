-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_proposition_2_3
-- name    : HermiteLaptop.MaxAgree.proposition_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:18:53.951339+00:00
-- url     : https://prove2.me/theorems/7b258c7c-363c-4879-8fee-ef1d0a053962
-- title:
--   Proposition 2.3 — multiset formula for c_{k,m}, and rational intervals for B_{a,λ} give rational bounds c̲_{k,m} ≤ c_{k,m} ≤ c̄_{k,m}
-- statement:
--   For every $k\ge2$ and $m\in\mathbb N_0$,
--   $$c_{k,m}=k\sum_{a=0}^m\ \sum_{\substack{\lambda:\ |\lambda|=m-a\\ \lambda\text{ a multiset of size }k-1}}N(\lambda)\,\frac{B_{a,\lambda}^2}{a!\prod_{b\in\lambda}b!}.$$
--   Moreover, if for every pair $(a,\lambda)$ in the sum we have a rational interval $I_{a,\lambda}\ni B_{a,\lambda}$, and $\underline b_{a,\lambda}=\min_{x\in I_{a,\lambda}}x^2$, $\overline b_{a,\lambda}=\max_{x\in I_{a,\lambda}}x^2$, then the quantities $\underline c_{k,m}$ and $\overline c_{k,m}$ obtained by replacing $B_{a,\lambda}^2$ with $\underline b_{a,\lambda}$, resp. $\overline b_{a,\lambda}$, are rational lower and upper bounds on $c_{k,m}$.
--
--   **Formalization Note.** Intervals are closed, $I_{a,\lambda}=[L,U]$ with $L,U\in\mathbb Q$, given by a function `Iv`; only the pairs in the sum are constrained. Rationality is stated as the existence of rationals equal to `cLowerCert k m Iv` and `cUpperCert k m Iv`.
--
--   Differences from the source:
--   - encoding: λ ranges over multisets of size k−1 with |λ| = m−a → λ ∈ multisetsOf (k−1) (m−a), the images in Multiset ℕ of the tuples Fin (k−1) → ℕ with sum m−a; reason: the same finite set of multisets
--   - encoding: a certified rational interval I_{a,λ} ∋ B_{a,λ} → rational endpoints (Iv a λ).1 ≤ B_{a,λ} ≤ (Iv a λ).2, closed interval; reason: min and max over I are those of a closed interval; L ≤ U follows
--   - encoding: "are certified rational lower and upper bounds" → c̲ ≤ c ≤ c̄ and both c̲, c̄ equal to rational numbers; reason: the two clauses of the claim
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 16 (PDF 19), Proposition 2.3

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_OneDim

namespace HermiteLaptop.MaxAgree

/-- Proposition 2.3: for `k ≥ 2`, the multiset formula
`c_{k,m} = k Σ_a Σ_λ N(λ) B_{a,λ}²/(a! Π_{b∈λ} b!)`; and rational intervals `I_{a,λ} ∋ B_{a,λ}`
give rational bounds `c̲_{k,m} ≤ c_{k,m} ≤ c̄_{k,m}`. -/
theorem proposition_2_3 (k : ℕ) (hk : 2 ≤ k) (m : ℕ) :
    coeffC k m = (k : ℝ) * ∑ a ∈ Finset.range (m + 1), ∑ lam ∈ multisetsOf (k - 1) (m - a),
      Nmult lam * Bal a lam ^ 2 / factDen a lam ∧
    ∀ Iv : ℕ → Multiset ℕ → ℚ × ℚ,
      (∀ a ≤ m, ∀ lam ∈ multisetsOf (k - 1) (m - a),
        ((Iv a lam).1 : ℝ) ≤ Bal a lam ∧ Bal a lam ≤ ((Iv a lam).2 : ℝ)) →
      cLowerCert k m Iv ≤ coeffC k m ∧ coeffC k m ≤ cUpperCert k m Iv ∧
      (∃ q : ℚ, (q : ℝ) = cLowerCert k m Iv) ∧ (∃ q : ℚ, (q : ℝ) = cUpperCert k m Iv) := by sorry

end HermiteLaptop.MaxAgree
