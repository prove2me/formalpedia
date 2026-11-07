-- Prove2me | Theorems.Thm_HypercliqueFalse_strassen_rectangular
-- name    : HypercliqueFalse.strassen_rectangular
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:30:54.970233+00:00
-- url     : https://prove2.me/theorems/445b2eef-c164-424a-b2fc-c36d543d9f4c
-- title:
--   Proof of Lemma 3.3 — Strassen: $\mathrm{MM}(n,d,m) = O(nm\,d^{\log_2 7-2})$ for $d\le n,m$
-- statement:
--   Rectangular integer matrices can be multiplied with Strassen's algorithm by splitting into square $d\times d$ blocks: for $d \le n$ and $d \le m$, the product of an $n\times d$ and a $d\times m$ integer matrix is computed on the word RAM in time
--   $$
--   \mathrm{MM}(n, d, m) = O\big(n\,m\,d^{\log_2 7 - 2}\big).
--   $$
--
--   The base cases (Lemma 3.3 for $h = 3$, the first algorithm of Lemma 4.3 and the base case $h = 2$) use this bound; with $\epsilon_2 = 3 - \log_2 7$ it reads $O(nm\,d^{1-\epsilon_2})$.
--
--   Differences from the source:
--   - generalization: MM(n, d, m) = O(nm d^{0.81}) → time O(n·m·d^{log₂ 7 − 2}); reason: log₂ 7 − 2 ≈ 0.807 < 0.81, so for d ≥ 1 this implies the printed bound (at d = 0 both bounds are 0); it is the exponent the proof of Lemma 4.3 uses
--   - reading: word RAM with words of Θ(log n) bits, all integers polynomially bounded (p.4) → SolvedWithin: for every integer-bound exponent κ one program, correct at every word width W ≥ b(⌊log₂ s⌋+1) on every instance of scale s with integers at most s^κ, within C·bound + C steps, the bound in the instance's own dimensions (each at most s); reason: the paper runs subroutines on small blocks of a size-n instance with the size-n word RAM (Lemma 4.2, Lemma 4.3, proof of Theorem 2.1), so hypotheses and conclusions must cover instances smaller than the scale; at dimension = scale this is the plain statement, and every-width correctness is the published machine's convention for Θ(log n)-bit words (the paper's algorithms only add, subtract and multiply polynomially bounded integers)
--   - encoding: d ≤ n, m → d ≤ n ≤ s, d ≤ m ≤ s; reason: n, m ≤ s is the scale of the reading above; d = 0 is allowed, where the bound is 0 and the output cells already hold the zero product
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Lemma 3.3, p.8; proof of Lemma 4.3, p.12

import Mathlib
import Definitions.Def_HypercliqueFalse_SolvedWithin
import Definitions.Def_HypercliqueFalse_matMul

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Strassen's algorithm, rectangular form: `MM(n, d, m) = O(n m d^{log₂ 7 − 2})` for
`d ≤ n, m`.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Lemma 3.3, p.8: "It suffices to use
Strassen's algorithm [Str69], which multiplies two d × d matrices in time O(d^{log₂ 7}) = O(d^{2.81}).
Hence, splitting into square blocks gives MM(n, d, m) = O(nm d^{0.81}) whenever d ≤ n, m"; used with
this exponent in the proof of Lemma 4.3, p.12 ("Using Strassen's algorithm, this takes time
O(N⁴n^{h−3}abc^{1−ϵ₂})", ϵ₂ = 3 − log₂ 7).

**Formalization Note.** An instance of `matMul` is `⟨n, m, d, _, X, Y⟩` (`x.1 = n`, `x.2.1 = m`,
`x.2.2.1 = d`). The exponent `log₂ 7 − 2 ≈ 0.807` is below the printed `0.81`. -/
theorem strassen_rectangular :
    SolvedWithin matMul
      (fun _ x => (x.1 : ℝ) * (x.2.1 : ℝ) * (x.2.2.1 : ℝ) ^ (Real.logb 2 7 - 2)) := by sorry

end HypercliqueFalse
