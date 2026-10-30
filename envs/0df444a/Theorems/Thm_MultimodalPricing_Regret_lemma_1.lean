-- Prove2me | Theorems.Thm_MultimodalPricing_Regret_lemma_1
-- name    : MultimodalPricing.Regret.lemma_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T08:02:29.999982+00:00
-- url     : https://prove2.me/theorems/65fa307f-87ec-45d5-ab72-c731098dedf3
-- title:
--   Lemma 1 — local polynomial approximation
-- statement:
--   Suppose $f\in\Sigma^k([p_{\min},p_{\max}];C)$ and $[a,b]\subseteq[p_{\min},p_{\max}]$ with $a\le b$ and $b-a\le1$. There exists a coefficient vector $c\in\mathbb R^k$ such that
--   $$|c_q|q!\le C\quad(0\le q<k),\qquad |f(p)-\sum_{q<k}c_q(p-a)^q|\le C(b-a)^k\quad(p\in[a,b]).$$
--   The polynomial may have a zero leading coefficient. Both the factorial coefficient bound and the uniform approximation guarantee are asserted.
--
--   Differences from the source:
--   - generalization: economic price interval → arbitrary finite real endpoints with a ≤ b, including a singleton; reason: all nonnegative nondegenerate source intervals are included without changing any formula
--   - encoding: (k−1) derivatives on the closed price interval → a tower of successive HasDerivWithinAt derivatives, with order zero equal to f on the interval; reason: uses one-sided endpoint derivatives, imposes no condition outside the interval, and at k=1 requires only the printed bounded Lipschitz condition
--   - encoding: a degree-(k−1) polynomial and a supremum error bound → a vector of k coefficients and a pointwise bound for every interval price; reason: matches the displayed polynomial, permits lower degree, and is equivalent to the bounded nonempty supremum assertion
-- source:
--   Wang, Chen, Simchi-Levi, Multi-Modal Dynamic Pricing, https://doi.org/10.1287/mnsc.2020.3819, supplied artifact (published metadata; SSRN 3489355 footer), Lemma 1, printed/PDF p. 12

import Definitions.Def_MultimodalPricing_Regret_Smooth

open MultimodalPricing.Regret

namespace MultimodalPricing.Regret

theorem lemma_1
    (k : ℕ) (C pmin pmax a b : ℝ) (f : ℝ → ℝ)
    (hf : Smooth k C pmin pmax f)
    (hab : a ≤ b) (hleft : pmin ≤ a) (hright : b ≤ pmax) (hwidth : b - a ≤ 1) :
    ∃ c : Fin k → ℝ,
      (∀ q : Fin k, |c q| * (q.val.factorial : ℝ) ≤ C) ∧
      ∀ p ∈ Set.Icc a b, |f p - localPolynomial k a c p| ≤ C * (b - a) ^ k := by sorry

end MultimodalPricing.Regret
