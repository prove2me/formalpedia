-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_4_17
-- name    : OptTwoSrcExt.Supplement.theorem_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:42:18.480036+00:00
-- url     : https://prove2.me/theorems/5d945715-f66a-4676-b090-90cb11c5622a
-- title:
--   Theorem 4.17 (= Theorem 1.6) — explicit sumset extractor with output exactly $k-2\lceil\log(1/\varepsilon)\rceil-8$
-- statement:
--   For every fixed $0<\delta\le1$ there are $b_\delta>0$ and $n_\delta$ such that, whenever $n\ge n_\delta$, $\delta n\le k\le n$ is an integer, and
--   $$2^{-b_\delta n}\le\varepsilon\le1/4,$$
--   there is an explicit deterministic polynomial-time map
--   $$\mathrm{SumExt}_{n,k,\varepsilon}:\mathbb F_2^n\to\mathbb F_2^m,\qquad m=k-2\lceil\log(1/\varepsilon)\rceil-8,$$
--   whose output on $X+Y$ is $\varepsilon$-close to uniform for all independent $X,Y$ on $\mathbb F_2^n$ with $H_\infty(X),H_\infty(Y)\ge k$. In particular $m\ge k-2\log(1/\varepsilon)-10$.
--
--   The constants in the running time and the nontrivial error range may depend on $\delta$, but the output-loss constants $2$ and $8$ do not. The entropy loss $2\log(1/\varepsilon)+O(1)$ matches the loss of the best seeded extractors.
--
--   **Formalization Note** $b_\delta$, $n_\delta$ and the machine are chosen after $\delta$ and before $n,k,\varepsilon$. The output length is stated exactly (as an integer identity) and the "in particular" bound as a further conjunct. Logarithms are base 2 and $\lceil\cdot\rceil$ is the integer ceiling.
--
--   Differences from the source:
--   - reading: explicit / deterministic polynomial-time map depending on k and ε → one LowErrExt.IsPolyTime machine per fixed parameter tuple, chosen before n, k, ε, run on [1^k, 1^{⌈log₂(1/ε)⌉}, inputs]; the map depends on ε only through ⌈log₂(1/ε)⌉; reason: the paper takes the accuracy exponent as an integer (§4.1.6, p.86) and running time polynomial in n + log(1/ε); this is the reading of the published goal theorem_1_5
--   - encoding: independent sources with H∞ ≥ k → arbitrary probability mass functions on 𝔽₂ⁿ with minEntropy ≥ k, law of the pair = indepPair; reason: published FuzzyExtractors.Hamming / LowErrExt definitions; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 4.17, pp.99–100 (PDF pp.101–102); introduced as Theorem 1.6, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_OptTwoSrcExt_machineVec

open FuzzyExtractors.Hamming LowErrExt OptTwoSrcExt

namespace OptTwoSrcExt.Supplement

/-- **Theorem 4.17 (Near-optimal sumset output) (= Theorem 1.6).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 4.17, printed pp.99–100 (PDF pp.101–102): "For
every fixed 0 < δ ⩽ 1 there are bδ > 0 and nδ such that, whenever n ⩾ nδ, δn ⩽ k ⩽ n is an integer,
and 2^{−bδn} ⩽ ε ⩽ 1/4, there is an explicit deterministic polynomial-time map
SumExt_{n,k,ε} : F_2^n → F_2^m, m = k − 2⌈log(1/ε)⌉ − 8, whose output on X + Y is ε-close to uniform
for all independent X, Y with H∞(X), H∞(Y) ⩾ k. In particular, m ⩾ k − 2 log(1/ε) − 10. The
constants in the running time and the nontrivial error range may depend on δ, but the displayed
output-loss constants do not." Introduced as Theorem 1.6, printed p.4 (PDF p.6).

For `0 < δ ≤ 1` there are `b > 0`, `n₀` and one polynomial-time machine `Fm` such that for all
`n ≥ n₀`, integers `δn ≤ k ≤ n` and reals `2^{−bn} ≤ ε ≤ 1/4`, with `s = ⌈log₂(1/ε)⌉` and
`SumExt(z) = Fm [1^k, 1^s, z]` on `z ∈ 𝔽₂ⁿ`, there is `m` with `m = k − 2s − 8` (as integers) such
that `SumExt` outputs exactly `m` bits, `Δ(SumExt(X + Y), U_m) ≤ ε` for all independent `X, Y` on
`𝔽₂ⁿ` with `H∞(X), H∞(Y) ≥ k`, and `m ≥ k − 2 log₂(1/ε) − 10`.

**Formalization Note.** `b, n₀` and the machine are chosen after `δ` and before `n, k, ε`; the output
length is exactly `k − 2⌈log₂(1/ε)⌉ − 8` with the constants `2` and `8` fixed. "Explicit
deterministic polynomial-time" follows the base mission's reading of the goal: one
`LowErrExt.IsPolyTime` machine with `k` and `⌈log₂(1/ε)⌉` in unary before the input `z` (written as a
bit list, `bitsOfVec`); outputs are read with `machineVec`. The "in particular" bound is stated as a
conjunct. Sources are arbitrary probability mass functions. -/
theorem theorem_4_17 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ b : ℝ, 0 < b ∧ ∃ n₀ : ℕ, ∃ Fm : List (List Bool) → List Bool, IsPolyTime Fm ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, δ * n ≤ k → k ≤ n →
        ∀ ε : ℝ, (2 : ℝ) ^ (-(b * n)) ≤ ε → ε ≤ 1 / 4 →
          ∃ m : ℕ, (m : ℤ) = (k : ℤ) - 2 * (⌈Real.logb 2 (1 / ε)⌉₊ : ℤ) - 8 ∧
            (∀ z : Fin n → ZMod 2, (Fm [List.replicate k true,
              List.replicate ⌈Real.logb 2 (1 / ε)⌉₊ true, bitsOfVec z]).length = m) ∧
            (∀ X Y : PMF (Fin n → ZMod 2), (k : ℝ) ≤ minEntropy X → (k : ℝ) ≤ minEntropy Y →
              statDist ((indepPair X Y).map fun p => machineVec Fm m [List.replicate k true,
                  List.replicate ⌈Real.logb 2 (1 / ε)⌉₊ true, bitsOfVec (p.1 + p.2)])
                (PMF.uniformOfFintype (Fin m → ZMod 2)) ≤ ε) ∧
            (k : ℝ) - 2 * Real.logb 2 (1 / ε) - 10 ≤ m := by sorry

end OptTwoSrcExt.Supplement
