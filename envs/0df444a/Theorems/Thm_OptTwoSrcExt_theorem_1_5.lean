-- Prove2me | Theorems.Thm_OptTwoSrcExt_theorem_1_5
-- name    : OptTwoSrcExt.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:35.319159+00:00
-- url     : https://prove2.me/theorems/25b6c767-b724-4f53-9f95-19f0081b016f
-- title:
--   Theorem 1.5 — explicit two-source extractor for min-entropy $\delta n$ with error $\varepsilon\ge2^{-b_\delta n}$ and output $2k-C_0\log(1/\varepsilon)-C_1$
-- statement:
--   There are absolute constants $C_0,C_1>0$ such that for every constant $0<\delta\le1$ there are constants $b_\delta>0$ and $n_\delta$ with the following property. For all $n\ge n_\delta$, every integer $k$ with $\delta n\le k\le n$, and every $\varepsilon$ with $2^{-b_\delta n}\le\varepsilon\le1/4$, there is an explicit two-source extractor $\mathrm{TExt}:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^m$ such that for any two independent sources $X,Y$ on $\{0,1\}^n$ with $H_\infty(X),H_\infty(Y)\ge k$,
--   $$\Delta\big(\mathrm{TExt}(X,Y),U_m\big)\le\varepsilon,\qquad m\ge2k-C_0\log(1/\varepsilon)-C_1 .$$
--   For each fixed $\delta$ the extractor is computed by one polynomial-time algorithm, in time polynomial in $n+\log(1/\varepsilon)$. Logarithms are base 2.
--
--   The output length $2k-O(\log(1/\varepsilon))$ and the error range down to $2^{-\Omega(n)}$ match the probabilistic bound up to the constants, for every constant entropy rate; previously error $2^{-\Omega(n)}$ was known only for entropy rate above about $4/9$ (Bourgain 2005, Lewko 2019).
--
--   **Formalization Note** $C_0,C_1$ are chosen before $\delta$; $b_\delta$, $n_\delta$ and the algorithm are chosen after $\delta$ and before $n,k,\varepsilon$. The algorithm is one polynomial-time Turing machine $F$, and $\mathrm{TExt}(x,y)=F[1^k,1^{\lceil\log(1/\varepsilon)\rceil},x,y]$: it receives $k$ and the integer accuracy exponent in unary, as the paper describes (Theorem 4.3, §4.1.6). Sources are arbitrary distributions, not only flat ones.
--
--   Differences from the source:
--   - reading: explicit two source extractor TExt for each n, k, ε (computable by a polynomial-time algorithm) → one polynomial-time machine F per δ, chosen before n, k, ε, with TExt(x, y) = F [1^k, 1^⌈log₂(1/ε)⌉, x, y]; reason: the paper's own explicitness (Theorem 4.3: polynomial in n + log(1/ε); §4.1.6: the algorithm takes the integer accuracy exponent); a per-instance reading is empty since every finite function is computable
--   - generalization: two independent (n, k) sources (min-entropy exactly k, p.1) → independent sources with min-entropy at least k; reason: Theorem 4.3's form; sources of min-entropy exactly k are a special case
--   - encoding: TExt : {0,1}^n × {0,1}^n → {0,1}^m → a function on bit lists with exactly m output bits on n-bit inputs (LowErrExt.IsTwoSourceExtList); reason: one function for all n, as explicitness requires; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 1.5, p.3 (PDF p.5); restated as Theorem 4.3, p.83 (PDF p.85); §4.1.6, p.86 (PDF p.88)

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_LowErrExt_IsTwoSourceExtList

open LowErrExt

namespace OptTwoSrcExt

/-- **Theorem 1.5 (= Theorem 4.3): explicit two-source extractor for any constant entropy rate,
with error `ε` and output length `2k − C₀ log(1/ε) − C₁`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 1.5, printed p.3 (PDF p.5): "There are absolute
constants C0, C1 > 0 such that, for every constant 0 < δ ⩽ 1, there are constants bδ > 0 and nδ with
the following property. For all n ⩾ nδ, integer δn ⩽ k ⩽ n, and 2^{−bδn} ⩽ ε ⩽ 1/4, there is an
explicit two source extractor TExt : {0, 1}^n × {0, 1}^n −→ {0, 1}^m such that, for any two
independent (n, k) sources X, Y, ∆(TExt(X, Y), Um) ⩽ ε, m ⩾ 2k − C0 log(1/ε) − C1."
Restated as Theorem 4.3, printed p.83 (PDF p.85), with "for independent X, Y with H∞(X), H∞(Y) ⩾ k"
and "For each fixed δ, construction and evaluation are polynomial in n + log(1/ε)"; §4.1.6, printed
p.86 (PDF p.88): "For an arbitrary real accuracy request, it is enough to construct for
2^{−⌈log(1/ε)⌉} … Thus the algorithm can take the accuracy exponent as an integer."

There are `C₀, C₁ > 0` such that for every `0 < δ ≤ 1` there are `b > 0`, `n₀` and one polynomial-time
machine `F` such that for all `n ≥ n₀`, all integers `k` with `δn ≤ k ≤ n`, and all real `ε` with
`2^{−bn} ≤ ε ≤ 1/4`, the function `TExt(x, y) = F [1^k, 1^{⌈log₂(1/ε)⌉}, x, y]` on `{0,1}ⁿ × {0,1}ⁿ`
outputs exactly `m` bits for some `m ≥ 2k − C₀ log₂(1/ε) − C₁`, and `Δ(TExt(X, Y), U_m) ≤ ε` for all
independent `X, Y` with `H∞(X), H∞(Y) ≥ k`.

**Formalization Note.** Quantifier order: `C₀, C₁` are absolute (chosen before `δ`); `b, n₀` and the
machine `F` are chosen after `δ` and before `n, k, ε`. "Explicit" is one `LowErrExt.IsPolyTime`
machine (Mathlib's `Turing.TM2ComputableInPolyTime`) per rate `δ`, whose inputs are `k` and the
integer accuracy exponent `⌈log₂(1/ε)⌉` in unary followed by the two `n`-bit inputs, so its running time
is polynomial in `n + log(1/ε)` (as Theorem 4.3 and §4.1.6 state); the extractor depends on `ε` only
through `⌈log₂(1/ε)⌉`. `(n, k)` sources are sources with min-entropy at least `k` (Theorem 4.3),
arbitrary probability mass functions, not only flat ones. The two-source property on bit lists is the
published `LowErrExt.IsTwoSourceExtList` (exact output length `m` on `n`-bit inputs). Logarithms are
base 2. -/
theorem theorem_1_5 :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∃ b : ℝ, 0 < b ∧ ∃ n₀ : ℕ, ∃ F : List (List Bool) → List Bool, IsPolyTime F ∧
          ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, δ * n ≤ k → k ≤ n →
            ∀ ε : ℝ, (2 : ℝ) ^ (-(b * n)) ≤ ε → ε ≤ 1 / 4 →
              ∃ m : ℕ, 2 * (k : ℝ) - C₀ * Real.logb 2 (1 / ε) - C₁ ≤ m ∧
                IsTwoSourceExtList n k m ε (fun x y =>
                  F [List.replicate k true, List.replicate ⌈Real.logb 2 (1 / ε)⌉₊ true, x, y]) := by sorry

end OptTwoSrcExt
