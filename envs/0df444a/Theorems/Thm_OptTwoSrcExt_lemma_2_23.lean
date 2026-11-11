-- Prove2me | Theorems.Thm_OptTwoSrcExt_lemma_2_23
-- name    : OptTwoSrcExt.lemma_2_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:33.136027+00:00
-- url     : https://prove2.me/theorems/9d093758-87a3-4614-9f53-21d36ba88936
-- title:
--   Lemma 2.23 — explicit strong seeded extractor with output $k-A(s+1)$ and seed $B[\log^2(n+2)+(s+1)\log(2+n/(s+1))]$
-- statement:
--   There are absolute constants $A,B>0$ such that for every $n$, every integer $0\le k\le n$ and every $0<\zeta\le1/4$, writing $s=\log(1/\zeta)$, there is a strong seeded extractor $E:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with error at most $\zeta$ for min-entropy $k$,
--   $$\Delta\big((U_d,E(X,U_d)),U_{d+m}\big)\le\zeta\quad\text{whenever } H_\infty(X)\ge k,$$
--   with output length $m\ge\lfloor k-A(s+1)\rfloor$ and seed length
--   $$d\le B\Big[\log^2(n+2)+(s+1)\log\Big(2+\frac{n}{s+1}\Big)\Big].$$
--   The extractor is computed in deterministic polynomial time in $n+s$, by one algorithm for all parameters. Logarithms are base 2.
--
--   This supplies both payload extractors $E_L,E_R$ of the construction of Theorem 1.5; the seed length is sublinear in $n$ when $s\le b n$ for small $b$.
--
--   **Formalization Note** One polynomial-time machine $F$, chosen after $A,B$, computes $E(x,v)=F[1^k,1^{\lceil s\rceil},x,v]$; it sees $\zeta$ only through the integer accuracy exponent $\lceil\log(1/\zeta)\rceil$, given in unary (the paper's convention, §4.1.6). Since $m\ge0$, the bound $m\ge\lfloor k-A(s+1)\rfloor$ is the printed "$\max\{0,k-A(s+1)\}$ up to an integer floor".
--
--   Differences from the source:
--   - reading: deterministic polynomial-time in n + s → one polynomial-time machine F, chosen after A, B, with E(x, v) = F [1^k, 1^⌈s⌉, x, v]; reason: the paper's convention for a real accuracy request (§4.1.6, p.86): the algorithm takes the integer accuracy exponent
--   - reading: Ignored seed padding and output truncation preserve the conclusion → not restated; reason: a remark valid for every strong seeded extractor, not part of the existence claim (paper.md decision 11)
--   - encoding: integer k ⩽ n; output length at least max{0, k − A(s + 1)} up to an integer floor → k : ℕ with k ≤ n; m : ℕ with ⌊k − A(s+1)⌋ ≤ m; reason: min-entropy is nonnegative, so a negative threshold gives the same instance as k = 0 (bound 0 in both); m ≥ 0 supplies the max with 0
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Lemma 2.23, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_IsPolyTime

open FuzzyExtractors.Hamming LowErrExt

namespace OptTwoSrcExt

/-- **Lemma 2.23 (Strong seeded extraction with near-total output).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Lemma 2.23, printed p.23 (PDF p.25): "There are absolute
A, B > 0 such that, for every n, integer k ⩽ n, and 0 < ζ ⩽ 1/4, there is a strong seeded extractor
with error at most ζ, output length at least max{0, k − A(s + 1)} up to an integer floor, and seed
length at most B [log²(n + 2) + (s + 1) log(2 + n/(s + 1))], s = log(1/ζ). (2.9) It is deterministic
polynomial-time in n + s."

There are `A, B > 0` and one polynomial-time machine `F` such that for every `n`, every integer
`0 ≤ k ≤ n` and every `0 < ζ ≤ 1/4`, with `s = log₂(1/ζ)`, there are a seed length `d` and an output
length `m` with `m ≥ ⌊k − A(s + 1)⌋`, `d ≤ B[log₂²(n + 2) + (s + 1) log₂(2 + n/(s + 1))]`, and the map
`E(x, v) = F [1^k, 1^{⌈s⌉}, x, v]` on `{0,1}ⁿ × {0,1}^d` outputs exactly `m` bits and is a strong
seeded `(k, ζ)` extractor: `Δ((E(X, U_d), U_d), (U_m, U_d)) ≤ ζ` for every `X` with `H∞(X) ≥ k`.

**Formalization Note.** Logarithms are base 2 and `log²(n + 2)` is `(log₂(n + 2))²` (rendered page).
"Deterministic polynomial-time in n + s" is one `LowErrExt.IsPolyTime` machine, chosen after `A, B`
and before `n, k, ζ`, whose inputs are `k` and the integer accuracy exponent `⌈s⌉` in unary followed
by the source and the seed (the paper's own convention, §4.1.6, p.86); the machine therefore sees
`ζ` only through `⌈log₂(1/ζ)⌉`. Since `m ≥ 0`, `m ≥ ⌊k − A(s + 1)⌋` is the printed
`max{0, k − A(s + 1)}` up to an integer floor. The strong-extractor property is the published
`FuzzyExtractors.Hamming.IsStrongExtractor` (the pair `(Ext(W; X), X)` against `(U_ℓ, X)`). -/
theorem lemma_2_23 :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ F : List (List Bool) → List Bool, IsPolyTime F ∧
      ∀ n k : ℕ, k ≤ n → ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 / 4 →
        ∃ d m : ℕ,
          ⌊(k : ℝ) - A * (Real.logb 2 (1 / ζ) + 1)⌋ ≤ (m : ℤ) ∧
          (d : ℝ) ≤ B * (Real.logb 2 ((n : ℝ) + 2) ^ 2 +
            (Real.logb 2 (1 / ζ) + 1) * Real.logb 2 (2 + (n : ℝ) / (Real.logb 2 (1 / ζ) + 1))) ∧
          (∀ (x : Fin n → Bool) (v : Fin d → Bool),
            (F [List.replicate k true, List.replicate ⌈Real.logb 2 (1 / ζ)⌉₊ true,
              List.ofFn x, List.ofFn v]).length = m) ∧
          IsStrongExtractor (k : ℝ) ζ (fun (x : Fin n → Bool) (v : Fin d → Bool) =>
            listOut m (F [List.replicate k true, List.replicate ⌈Real.logb 2 (1 / ζ)⌉₊ true,
              List.ofFn x, List.ofFn v])) := by sorry

end OptTwoSrcExt
