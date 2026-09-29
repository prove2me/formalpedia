-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_equal_subintervals_degree
-- name    : NHPPArrivals.LinearRate.equal_subintervals_degree
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:22:02.010187+00:00
-- url     : https://prove2.me/theorems/9158b6bc-9b47-448d-b239-3ff72a7a0380
-- title:
--   THEOREM 5 — combining k equal subintervals of a linear rate: D = Σ p_j D_j ≤ C/k (20)–(22)
-- statement:
--   Let $\lambda(t) = a + bt$ be a linear arrival rate on $[0,T]$ with $T > 0$, $a \ge 0$, $b \ge 0$, and not identically zero. For $k \ge 1$, divide $[0,T]$ into $k$ subintervals of length $T/k$, and combine the data of all subintervals after rescaling each to $[0,1]$; by LEMMA 1 the combined data have the conditional cdf $F = \sum_{j=1}^k p_j F_j$. Let $r_j = b/\lambda((j-1)T/k)$ be the relative slope on the $j$-th subinterval.
--
--   There is a constant $C$ (depending on $a$, $b$, $T$ but not on $k$) such that for every $k \ge 1$, all suprema below are attained and
--   $$D \equiv \sup_{0 \le t \le 1} |F(t) - t| = \sum_{j=1}^k p_j D_j = \sum_{j=1}^k p_j \sup_{0 \le t \le 1} |F_j(t) - t|, \tag{20}$$
--   if $a > 0$,
--   $$D = \sum_{j=1}^k \frac{p_j\, r_j T/k}{8 + 4 r_j T/k}, \tag{21}$$
--   if $a = 0$,
--   $$D = \frac{p_1}{4} + \sum_{j=2}^k \frac{p_j/(j-1)}{8 + 4/(j-1)}, \tag{22}$$
--   and in both cases
--   $$D \le \frac{C}{k}.$$
--
--   So combining equally spaced subintervals drives the degree of nonhomogeneity of a linear rate to zero at rate $1/k$. This is what justifies the paper's practical recommendation to test the Poisson hypothesis on short subintervals and combine the data.
--
--   **Formalization Note** The constant $C$ is quantified before $k$, as in "$\le C/k$ for all $k \ge 1$ for a constant $C$"; one $C$ serves both cases, since only one case applies to given $a$. $b \ge 0$ is §3.3's standing assumption; "$a > 0$ or $b > 0$" excludes the identically zero rate, excluded by §3.2. The summand of (21) is read as $p_j \cdot (r_j T/k)/(8 + 4 r_j T/k)$, which is $p_j D_j$ by THEOREM 4. $F$, $F_j$, $p_j$ and $r_j$ are the general definitions of (17)–(18) applied to $\lambda(t) = a + bt$, not their closed forms.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, p. 473, THEOREM 5, (20), (21), (22)

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

namespace NHPPArrivals.LinearRate

theorem equal_subintervals_degree (a b T : ℝ) (hT : 0 < T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      IsGreatest ((fun t => |mixCdf (linRate a b) T k t - t|) '' Set.Icc (0:ℝ) 1)
        (degree (mixCdf (linRate a b) T k)) ∧
      (∀ j ∈ Finset.Icc 1 k,
        IsGreatest ((fun t => |subCdf (linRate a b) T k j t - t|) '' Set.Icc (0:ℝ) 1)
          (degree (subCdf (linRate a b) T k j))) ∧
      degree (mixCdf (linRate a b) T k) =
        ∑ j ∈ Finset.Icc 1 k,
          weight (linRate a b) T k j * degree (subCdf (linRate a b) T k j) ∧
      (0 < a → degree (mixCdf (linRate a b) T k) =
        ∑ j ∈ Finset.Icc 1 k,
          weight (linRate a b) T k j * (subSlope a b T k j * T / k) /
            (8 + 4 * subSlope a b T k j * T / k)) ∧
      (a = 0 → degree (mixCdf (linRate a b) T k) =
        weight (linRate a b) T k 1 / 4 +
          ∑ j ∈ Finset.Icc 2 k,
            (weight (linRate a b) T k j / ((j:ℝ) - 1)) / (8 + 4 / ((j:ℝ) - 1))) ∧
      degree (mixCdf (linRate a b) T k) ≤ C / k := by sorry

end NHPPArrivals.LinearRate
