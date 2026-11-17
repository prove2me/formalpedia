-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_4_8
-- name    : OptTwoSrcExt.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:41:49.017217+00:00
-- url     : https://prove2.me/theorems/dcf6301d-2f22-4b07-b6fb-cc0d40e32f64
-- title:
--   Theorem 4.8 (= Theorem 1.7) — source-strong $C$-non-malleable extraction with output $k/(C+1)-O(\log(1/\varepsilon)+1)$
-- statement:
--   There is an absolute constant $A>0$ with the following property. For every fixed $\delta>0$ and integer $C\ge0$ there is $b_{\delta,C}>0$ such that, for sufficiently large $n$, every integer $\delta n\le k\le n$ and every
--   $$2^{-b_{\delta,C}n}\le\varepsilon\le1/4,$$
--   there is an explicit polynomial-time map $F:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^m$ with
--   $$m\ge\frac k{C+1}-A\big(\log(1/\varepsilon)+1\big)$$
--   such that, for every independent pair $X,Y$ with $H_\infty(X),H_\infty(Y)\ge k$ and every admissible $C$-tuple $(f_i,g_i)$,
--   $$\big(F(X,Y),(F(f_i(X),g_i(Y)))_{i=1}^C,Y\big)\approx_\varepsilon\big(U_m,(F(f_i(X),g_i(Y)))_{i=1}^C,Y\big),\tag{4.32}$$
--   $$\big(F(X,Y),(F(f_i(X),g_i(Y)))_{i=1}^C,X\big)\approx_\varepsilon\big(U_m,(F(f_i(X),g_i(Y)))_{i=1}^C,X\big).\tag{4.33}$$
--   The uniform variable is independent of everything else displayed, and the same function satisfies both comparisons. The additive output-loss constant $A$ is absolute; the error range and running time may depend on $\delta,C$.
--
--   For $C=0$ this is a two-source extractor strong in either source separately with output $k-O(\log(1/\varepsilon)+1)$.
--
--   **Formalization Note** $A$ is chosen before $\delta,C$; $b$, the length threshold and the machine after $\delta,C$ and before $n,k,\varepsilon$. Admissible tamperings are those of Definition 2.2. The property is `IsSourceStrongNM` of this supplement. Logarithms are base 2.
--
--   Differences from the source:
--   - reading: explicit / deterministic polynomial-time map depending on k and ε → one LowErrExt.IsPolyTime machine per fixed parameter tuple, chosen before n, k, ε, run on [1^k, 1^{⌈log₂(1/ε)⌉}, inputs]; the map depends on ε only through ⌈log₂(1/ε)⌉; reason: the paper takes the accuracy exponent as an integer (§4.1.6, p.86) and running time polynomial in n + log(1/ε); this is the reading of the published goal theorem_1_5
--   - encoding: m ⩾ k/(C + 1) − O(log(1/ε) + 1), "the additive output-loss constants can be taken absolute" → m ≥ k/(C + 1) − A(log₂(1/ε) + 1) with one A > 0 chosen before δ and C; reason: the O(·) constant is pinned by the theorem's own sentence
--   - encoding: independent sources with H∞ ≥ k → arbitrary probability mass functions on {0,1}ⁿ with minEntropy ≥ k, law of the pair = indepPair; reason: published FuzzyExtractors.Hamming / LowErrExt definitions; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 4.8, p.92 (PDF p.94); introduced as Theorem 1.7, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_OptTwoSrcExt_Supplement_IsNMExt

open LowErrExt

namespace OptTwoSrcExt.Supplement

/-- **Theorem 4.8 (Source-strong endpoint) (= Theorem 1.7).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 4.8, printed p.92 (PDF p.94): "For every fixed
δ > 0 and integer C ⩾ 0 there is bδ,C > 0 such that, for sufficiently large n, integer δn ⩽ k ⩽ n,
and 2^{−bδ,Cn} ⩽ ε ⩽ 1/4, there is an explicit polynomial-time map F : {0, 1}^n × {0, 1}^n →
{0, 1}^m with m ⩾ k/(C + 1) − O(log(1/ε) + 1) such that, for every independent min-entropy-k pair and
every admissible C-tuple, (F(X, Y), (F(fi(X), gi(Y)))_{i=1}^C, Y) ≈ε (Um, (F(fi(X), gi(Y)))_{i=1}^C, Y),
(4.32) (F(X, Y), (F(fi(X), gi(Y)))_{i=1}^C, X) ≈ε (Um, (F(fi(X), gi(Y)))_{i=1}^C, X). (4.33) The
uniform variable is independent of everything else displayed. The same function satisfies both
comparisons. The additive output-loss constants can be taken absolute; the error-range and
running-time constants may depend on δ, C." Introduced as Theorem 1.7, printed p.4 (PDF p.6).

There is an absolute `A > 0` such that for every `δ > 0` and integer `C ≥ 0` there are `b > 0`, `n₀`
and one polynomial-time machine `Fm` such that for all `n ≥ n₀`, integers `δn ≤ k ≤ n` and reals
`2^{−bn} ≤ ε ≤ 1/4`, the map `F(x, y) = Fm [1^k, 1^{⌈log₂(1/ε)⌉}, x, y]` outputs exactly `m` bits
for some `m ≥ k/(C + 1) − A(log₂(1/ε) + 1)` and is separately source strong `C`-non-malleable at
entropy `k` with error `ε` (Definition 2.3: both (4.32) and (4.33), for every admissible `C`-tuple,
with the actual tampered outputs and `U_m` independent of the displayed variables).

**Formalization Note.** `A` (the `O(·)` constant, "can be taken absolute") is chosen before `δ, C`;
`b, n₀` and the machine after `δ, C` and before `n, k, ε`. "Explicit polynomial-time" is the base
mission's reading of the goal: one `LowErrExt.IsPolyTime` machine whose inputs are `k` and
`⌈log₂(1/ε)⌉` in unary, then the two `n`-bit inputs; the map depends on `ε` only through
`⌈log₂(1/ε)⌉`. "Min-entropy-`k` pair" means min-entropy at least `k`; sources are arbitrary
probability mass functions. Admissible tamperings are those of Definition 2.2
(`Pr[(f_i(X), g_i(Y)) = (X, Y)] = 0`). `C = 0` is included. -/
theorem theorem_4_8 :
    ∃ A : ℝ, 0 < A ∧ ∀ δ : ℝ, 0 < δ → ∀ C : ℕ,
      ∃ b : ℝ, 0 < b ∧ ∃ n₀ : ℕ, ∃ Fm : List (List Bool) → List Bool, IsPolyTime Fm ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, δ * n ≤ k → k ≤ n →
          ∀ ε : ℝ, (2 : ℝ) ^ (-(b * n)) ≤ ε → ε ≤ 1 / 4 →
            ∃ m : ℕ, (k : ℝ) / (C + 1) - A * (Real.logb 2 (1 / ε) + 1) ≤ m ∧
              (∀ x y : Fin n → Bool, (Fm [List.replicate k true,
                List.replicate ⌈Real.logb 2 (1 / ε)⌉₊ true, List.ofFn x, List.ofFn y]).length = m) ∧
              IsSourceStrongNM C k ε (fun x y : Fin n → Bool => listOut m (Fm [List.replicate k true,
                List.replicate ⌈Real.logb 2 (1 / ε)⌉₊ true, List.ofFn x, List.ofFn y])) := by sorry

end OptTwoSrcExt.Supplement
