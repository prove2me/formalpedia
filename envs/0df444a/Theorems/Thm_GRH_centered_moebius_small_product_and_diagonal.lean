-- Prove2me | Theorems.Thm_GRH_centered_moebius_small_product_and_diagonal
-- name    : GRH.centered_moebius_small_product_and_diagonal
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:14:26.849437+00:00
-- url     : https://prove2.me/theorems/8163e66a-72ab-513e-be36-e573188d5de4
-- title:
--   Uniform absolute bound for the small-product pairs and the diagonal in the centered Möbius sum
-- statement:
--   Write $U=\lfloor\sqrt N\rfloor$. Let $A_{d,e}$ count the positive integers $r\le N/(de)$ with $der\equiv a\bmod q$. Put
--   $$
--   w_{d,e}=\mu(d)\mu(e)\left(A_{d,e}-\mathbf 1_{(de,q)=1}\frac{N}{qde}\right).
--   $$
--
--   For every $\sigma>1/2$ there is a constant $K_\sigma\ge0$ such that, for every positive modulus $q$, every unit residue $a\bmod q$, and every $N\ge0$,
--   $$
--   \sum_{\substack{1\le d,e\le U\\de\le U\ \mathrm{or}\ d=e}}|w_{d,e}|
--   \le K_\sigma(N+1)^\sigma.
--   $$
--   A diagonal pair below the hyperbola occurs once. The constant is uniform in $q$ and $a$.
-- source:
--   Companion to GRH.centered_moebius_progression_bilinear_power_bound, https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006. The finite truncation comes from Helfgott and Thompson, Summing μ(n): a faster elementary algorithm, §2, equations (2.1)–(2.2), https://doi.org/10.1007/s40993-022-00408-8. The absolute small-product and diagonal estimate follows from counting each row and summing a convergent p-series.

import Definitions.Def_GRH_MoebiusBilinear

open Finset
open scoped BigOperators

theorem GRH.centered_moebius_small_product_and_diagonal (σ : ℝ) (hhalf : (1/2 : ℝ) < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a → ∀ N : ℕ,
      (∑ d ∈ Ioc 0 N.sqrt,
        ∑ e ∈ (Ioc 0 N.sqrt).filter (fun e => d * e ≤ N.sqrt ∨ d = e),
          |(ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) *
          (GRH.moebiusProgressionCount q a N d e -
            if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
              (1 / (q : ℝ)) * N / ((d : ℝ) * e) else 0)|) ≤ K * ((N : ℝ) + 1) ^ σ := by sorry
