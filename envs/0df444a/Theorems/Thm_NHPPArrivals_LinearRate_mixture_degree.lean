-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_mixture_degree
-- name    : NHPPArrivals.LinearRate.mixture_degree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:21:29.369993+00:00
-- url     : https://prove2.me/theorems/21546d22-c21f-437e-a50b-0319b445ec46
-- title:
--   THEOREM 5 (20) — D = Σ p_j D_j for k equal subintervals of a linear rate
-- statement:
--   Let $\lambda(t) = a + bt$ on $[0,T]$ with $T > 0$, $a \ge 0$, $b \ge 0$ and $a > 0$ or $b > 0$. Divide $[0,T]$ into $k \ge 1$ subintervals of length $T/k$, with subinterval conditional cdfs $F_j$ and weights $p_j$ as in LEMMA 1, and let $F = \sum_{j=1}^k p_j F_j$ be the conditional cdf of the combined data. Then every supremum below is attained on $[0,1]$, and
--   $$D \equiv \sup_{0 \le t \le 1} |F(t) - t| = \sum_{j=1}^k p_j D_j = \sum_{j=1}^k p_j \sup_{0 \le t \le 1} |F_j(t) - t|.$$
--
--   The degree of nonhomogeneity of the combined data is thus the weighted average of the degrees of the subintervals, with the arrival shares as weights. This is the first display of THEOREM 5, for one fixed $k$, without the closed forms (21)–(22).
--
--   **Formalization Note** $b \ge 0$ is §3.3's standing assumption, and "$a > 0$ or $b > 0$" excludes the identically zero rate (§3.2). $a \ge 0$ covers the paper's two cases $a > 0$ and $a = 0$.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, p. 473, THEOREM 5, (20)

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

namespace NHPPArrivals.LinearRate

theorem mixture_degree (a b T : ℝ) (k : ℕ) (hT : 0 < T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) (hk : 1 ≤ k) :
    IsGreatest ((fun t => |mixCdf (linRate a b) T k t - t|) '' Set.Icc (0:ℝ) 1)
      (degree (mixCdf (linRate a b) T k)) ∧
    (∀ j ∈ Finset.Icc 1 k,
      IsGreatest ((fun t => |subCdf (linRate a b) T k j t - t|) '' Set.Icc (0:ℝ) 1)
        (degree (subCdf (linRate a b) T k j))) ∧
    degree (mixCdf (linRate a b) T k) =
      ∑ j ∈ Finset.Icc 1 k,
        weight (linRate a b) T k j * degree (subCdf (linRate a b) T k j) := by sorry

end NHPPArrivals.LinearRate
