-- Prove2me | Theorems.Thm_GRH_centered_moebius_large_product_upper_triangle_bound
-- name    : GRH.centered_moebius_large_product_upper_triangle_bound
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T08:14:27.207237+00:00
-- url     : https://prove2.me/theorems/45798063-cde7-4696-817b-c085c4176dbb
-- title:
--   Centered Möbius cancellation on the strict upper triangle above the square-root hyperbola
-- statement:
--   Fix a positive modulus $q$, a unit residue $a\bmod q$, and $1/2<\sigma<1$. For $U=\lfloor\sqrt N\rfloor$, write $A_{d,e}$ for the number of positive $r\le N/(de)$ satisfying $der\equiv a\bmod q$. The open estimate asks for a constant $C=C(q,a,\sigma)\ge0$ such that, for every $N\ge0$,
--   $$
--   \left|\sum_{\substack{1\le d<e\le U\\de>U}}\mu(d)\mu(e)
--   \left(A_{d,e}-\mathbf 1_{(de,q)=1}\frac{N}{qde}\right)\right|
--   \le C(N+1)^\sigma.
--   $$
--
--   Only distinct pairs above the hyperbola occur, with each unordered pair appearing once. Every $r$ occurring in these counts also satisfies $r\le U$, since $N<(U+1)^2$. The absolute value is outside the signed sum.
-- source:
--   Companion to GRH.centered_moebius_progression_bilinear_power_bound, https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006. The finite truncation comes from Helfgott and Thompson, Summing μ(n): a faster elementary algorithm, §2, equations (2.1)–(2.2), https://doi.org/10.1007/s40993-022-00408-8. The restricted signed estimate is a proposed open subproblem. The cited paper supplies the truncation.

import Definitions.Def_GRH_MoebiusBilinear

open Finset
open scoped BigOperators

theorem GRH.centered_moebius_large_product_upper_triangle_bound
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1/2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |∑ d ∈ Ioc 0 N.sqrt,
        ∑ e ∈ (Ioc 0 N.sqrt).filter (fun e => d < e ∧ N.sqrt < d * e),
          (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) *
          (GRH.moebiusProgressionCount q a N d e -
            if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
              (1 / (q : ℝ)) * N / ((d : ℝ) * e) else 0)| ≤ C * ((N : ℝ) + 1) ^ σ := by sorry
