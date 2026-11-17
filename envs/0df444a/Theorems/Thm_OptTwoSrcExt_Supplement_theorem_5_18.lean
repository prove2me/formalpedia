-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_5_18
-- name    : OptTwoSrcExt.Supplement.theorem_5_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:43:40.07931+00:00
-- url     : https://prove2.me/theorems/5eaa22a7-9df5-4df1-b3a7-0bda8f69e030
-- title:
--   Theorem 5.18 (= Theorem 1.9) — source-strong $t$-non-malleable extraction at entropy $C_{t,\vartheta}n/\log n$
-- statement:
--   There is an absolute constant $A>0$ with the following property. Fix an integer $t\ge0$ and $0<\vartheta<1/2$. There are constants $C_{t,\vartheta}>0$ and $n_0$ such that, for every $n\ge n_0$, every integer $C_{t,\vartheta}n/\log n\le k\le n$ and every
--   $$2^{-n^{1/2-\vartheta}}\le\varepsilon\le1/4,$$
--   there is an explicit polynomial-time $t$-non-malleable two-source extractor $F:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^m$ with
--   $$m\ge\frac k{t+1}-A\big(\log(1/\varepsilon)+1\big).$$
--   For every independent pair $X,Y$ with $H_\infty(X),H_\infty(Y)\ge k$ and every admissible $t$-tuple of separate tamperings, put $Z=(F(f_i(X),g_i(Y)))_{i=1}^t$. The same function satisfies
--   $$(F(X,Y),Z,Y)\approx_\varepsilon(U_m,Z,Y),\tag{5.22}$$
--   $$(F(X,Y),Z,X)\approx_\varepsilon(U_m,Z,X).\tag{5.23}$$
--   The uniform word is independent of the entire displayed marginal, and $Z$ consists of the actual $m$-bit comparison outputs. For $t=0$ this is ordinary extraction strong in either original source separately.
--
--   This extends the source-strong endpoint to entropy rate $O(1/\log n)$ with error down to $2^{-n^{1/2-\vartheta}}$.
--
--   **Formalization Note** $A$ is chosen before $t,\vartheta$; $C_{t,\vartheta}$, $n_0$ and the machine after $t,\vartheta$ and before $n,k,\varepsilon$. Logarithms are base 2. The $t$-non-malleability is stated with error $\varepsilon$ (it follows from either source-strong comparison by forgetting the retained source).
--
--   Differences from the source:
--   - reading: explicit / deterministic polynomial-time map depending on k and ε → one LowErrExt.IsPolyTime machine per fixed parameter tuple, chosen before n, k, ε, run on [1^k, 1^{⌈log₂(1/ε)⌉}, inputs]; the map depends on ε only through ⌈log₂(1/ε)⌉; reason: the paper takes the accuracy exponent as an integer (§4.1.6, p.86) and running time polynomial in n + log(1/ε); this is the reading of the published goal theorem_1_5
--   - encoding: m ⩾ k/(t + 1) − O(log(1/ε) + 1), "the implied additive-loss constant is absolute"; an explicit t-non-malleable two-source extractor (error unstated) → m ≥ k/(t + 1) − A(log₂(1/ε) + 1) with one A > 0 chosen before t and ϑ; IsNMExt t k ε together with IsSourceStrongNM t k ε; reason: the O(·) constant is pinned by the theorem; ordinary t-non-malleability with error ε follows from (5.22) by marginalizing the retained source
--   - encoding: independent sources with H∞ ≥ k → arbitrary probability mass functions on {0,1}ⁿ with minEntropy ≥ k, law of the pair = indepPair; reason: published FuzzyExtractors.Hamming / LowErrExt definitions; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 5.18, pp.115–116 (PDF pp.117–118); introduced as Theorem 1.9, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_OptTwoSrcExt_Supplement_IsNMExt

open LowErrExt

namespace OptTwoSrcExt.Supplement

/-- **Theorem 5.18 (Source-strong entropy-efficient output at rate C/log n) (= Theorem 1.9).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 5.18, printed pp.115–116 (PDF pp.117–118): "Fix an
integer t ⩾ 0 and 0 < ϑ < 1/2. There are constants Ct,ϑ > 0 and n0 such that, for every n ⩾ n0,
integer Ct,ϑn/ log n ⩽ k ⩽ n, and 2^{−n^{1/2−ϑ}} ⩽ ε ⩽ 1/4, there is an explicit polynomial-time
t-non-malleable two-source extractor F : {0, 1}^n × {0, 1}^n → {0, 1}^m with
m ⩾ k/(t + 1) − O(log(1/ε) + 1). The implied additive-loss constant is absolute. For every
independent min-entropy-k pair and every admissible t-tuple of separate tamperings, put
Z = (F(fi(X), gi(Y)))_{i=1}^t. The same function satisfies (F(X, Y), Z, Y) ≈ε (Um, Z, Y), (5.22)
(F(X, Y), Z, X) ≈ε (Um, Z, X). (5.23) The uniform word is independent of the entire displayed
marginal, and Z consists of the actual m-bit comparison outputs. For t = 0 this is ordinary
extraction strong in either original source separately." Introduced as Theorem 1.9, printed p.4
(PDF p.6).

There is an absolute `A > 0` such that for every integer `t ≥ 0` and `0 < ϑ < 1/2` there are
`C > 0`, `n₀` and one polynomial-time machine `Fm` such that for all `n ≥ n₀`, integers
`Cn/log₂ n ≤ k ≤ n` and reals `2^{−n^{1/2−ϑ}} ≤ ε ≤ 1/4`, the map
`F(x, y) = Fm [1^k, 1^{⌈log₂(1/ε)⌉}, x, y]` outputs exactly `m` bits for some
`m ≥ k/(t + 1) − A(log₂(1/ε) + 1)`, is a `t`-non-malleable two-source extractor at entropy `k` with
error `ε` (Definition 2.2), and satisfies both source-strong comparisons (5.22), (5.23) with error
`ε` (Definition 2.3).

**Formalization Note.** `A` is chosen before `t, ϑ`; `C, n₀` and the machine after `t, ϑ` and before
`n, k, ε`. Logarithms are base 2 (`log n = log₂ n`); `n^{1/2−ϑ}` is the real power. "Explicit
polynomial-time" is the base mission's reading of the goal: one `LowErrExt.IsPolyTime` machine with
`k` and `⌈log₂(1/ε)⌉` in unary before the two `n`-bit inputs. The error of the `t`-non-malleability
is `ε`, as for the displayed comparisons. Admissible tamperings are those of Definition 2.2; the
comparison tuple consists of the actual tampered outputs. Sources are arbitrary probability mass
functions with min-entropy at least `k`. `t = 0` is included. -/
theorem theorem_5_18 :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℕ, ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∃ Fm : List (List Bool) → List Bool, IsPolyTime Fm ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, C * n / Real.logb 2 n ≤ k → k ≤ n →
          ∀ ε : ℝ, (2 : ℝ) ^ (-((n : ℝ) ^ ((1 : ℝ) / 2 - ϑ))) ≤ ε → ε ≤ 1 / 4 →
            ∃ m : ℕ, (k : ℝ) / (t + 1) - A * (Real.logb 2 (1 / ε) + 1) ≤ m ∧
              (∀ x y : Fin n → Bool, (Fm [List.replicate k true,
                List.replicate ⌈Real.logb 2 (1 / ε)⌉₊ true, List.ofFn x, List.ofFn y]).length = m) ∧
              IsNMExt t k ε (fun x y : Fin n → Bool => listOut m (Fm [List.replicate k true,
                List.replicate ⌈Real.logb 2 (1 / ε)⌉₊ true, List.ofFn x, List.ofFn y])) ∧
              IsSourceStrongNM t k ε (fun x y : Fin n → Bool => listOut m (Fm [List.replicate k true,
                List.replicate ⌈Real.logb 2 (1 / ε)⌉₊ true, List.ofFn x, List.ofFn y])) := by sorry

end OptTwoSrcExt.Supplement
