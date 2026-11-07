-- Prove2me | Theorems.Thm_IntQuotHNP_lemma_4_3
-- name    : IntQuotHNP.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:57.83255+00:00
-- url     : https://prove2.me/theorems/9b698693-f1dc-4447-84bb-bee79f19a368
-- title:
--   Lemma 4.3 — $R$ is an exact deterministic reconstructor with $r=1$; uniqueness bound $4^N(X-1)^N/(p-1)^{N-1}$
-- statement:
--   1. On every promised input and for every $a\in\{0,\dots,X-1\}$, every element of $R(a)$ satisfies (4) with some $x\in B$, and $|R(a)|\le1$.
--   2. On every promised input, $R(x_1)=\{y\}$ for every consistent pair $(y,x)$; in particular $R(x_1^*)=\{y^*\}$.
--   3. One Turing machine computes $R(a)$ from the public input and $a$; for each $N$ there are constants $C,K$ such that it halts within $C(\log p)^K$ steps on every promised input with $N$ samples and every $a$, and the elements of $R(a)$ have binary codes of length at most $C(\log p)^K$.
--   4. For every prime $p$, $3\le N<p$, $1\le X<p$ and $y^*\in\mathbb Z_p$, under the sampling rule,
--   $$
--   \Pr\bigl[\text{some } y\ne y^*\text{ satisfies (4) with an error vector in } B\bigr]\le\frac{4^N(X-1)^N}{(p-1)^{N-1}} .
--   $$
--
--   The reconstructor makes the search's output exact, and the bound gives unique recovery with high probability.
--
--   Differences from the source:
--   - reading: R is a deterministic reconstructor with uniform expected bit cost poly(log p), Definition 3.1 (iii) → one Turing machine (OutputsWithin) halting within C(log p)^K steps, with C, K depending on N; reason: the paper names no machine; steps of a fixed multi-stack machine and bit operations are polynomially related, and the bounds are closed under polynomials; R is deterministic, so a uniform expected bound is a worst-case bound
--   - encoding: with probability one in Definition 3.1 (i), (ii) → always; reason: R is deterministic
--   - encoding: R(x*_1) = {y*} for the hidden pair → R(x_1) = {y} for every consistent pair (y, x); reason: this is Definition 3.1 (ii) for r = 1 and what the paper's proof shows; the hidden pair is one such pair
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 4.3, p.23 (PDF p.24); Definition 3.1, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_IntQuotHNP_MIHNPInput
import Definitions.Def_IntQuotHNP_Encoding
import Definitions.Def_IntQuotHNP_Sampling
import Definitions.Def_IntQuotHNP_Reconstructor

open ExponomialAssortment.FPTAS (encodeNat)
open HMBinPacking (OutputsWithin)

namespace IntQuotHNP

/-- **Lemma 4.3 (reconstruction and uniqueness).**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), Lemma 4.3, p.23 (PDF p.24): "On every promised input, R is a deterministic reconstructor
with r = 1 in the sense of Definition 3.1. In particular, R(x∗₁) = {y∗}. Under the sampling rule
above, the probability that some y ≠ y∗ satisfies (4) with an error vector in B is at most
4^N(X − 1)^N/(p − 1)^{N−1}."
Definition 3.1, p.16 (PDF p.17): "returns a set R(a) of at most r secret candidates … (i) Every
element of R(a) satisfies the original input constraints … (ii) For every secret y and
corresponding x ∈ B consistent with the input, Pr[y ∈ R(x₁)] = 1. (iii) For every public input and
every a ∈ B₁, computing R(a) has uniform expected bit cost poly(log p). Its elements have canonical
binary encodings of length poly(log p)."

1. On every promised input and every `a ∈ B₁ = {0, …, X − 1}`, every element of `R(a)` satisfies
   (4) with some `x ∈ B`, and `|R(a)| ≤ 1` (`r = 1`).
2. On every promised input, `R(x₁) = {y}` for every consistent pair `(y, x)`.
3. There is one Turing machine computing `R(a)` from the public input and `a`, and for each `N`
   constants `C, K` such that it halts within `C(log p)^K` steps on every promised input with `N`
   samples and every `a ∈ B₁`; the elements of `R(a)` have binary codes of length `≤ C(log p)^K`.
4. For every prime `p`, `3 ≤ N < p`, `1 ≤ X < p` and `y∗ ∈ ℤ_p`, under the sampling rule the
   probability that the sampled input has a secret `y ≠ y∗` satisfying (4) with `x ∈ B` is at most
   `4^N(X − 1)^N/(p − 1)^{N−1}`.

**Formalization Note.** `R` is deterministic, so "with probability one" is "always". The paper's
`x₁` is `x 0`. Bit cost is the step count of a Mathlib `Turing.TM2ComputableAux Bool Bool`
(`OutputsWithin`), with input the code of the public input followed by the code of `a`. `log` is
the natural logarithm; for fixed `N` the constants may depend on `N` (§3.1: "polynomial bounds may
depend on these fixed parameters"). -/
theorem lemma_4_3 :
    (∀ I : MIHNPInput, IsPromised I → ∀ a, a < I.X →
      reconstruct I a ⊆ solutionSet I ∧ (reconstruct I a).card ≤ 1) ∧
    (∀ I : MIHNPInput, IsPromised I → ∀ (h0 : 0 < I.N) (y : ℕ) (x : Fin I.N → ℕ),
      Consistent I y x → reconstruct I (x ⟨0, h0⟩) = {y}) ∧
    (∃ MR : Turing.TM2ComputableAux Bool Bool, ∀ N : ℕ, ∃ (C : ℝ) (K : ℕ),
      ∀ I : MIHNPInput, IsPromised I → I.N = N → ∀ a, a < I.X →
        (∃ s : ℕ, (s : ℝ) ≤ C * Real.log I.p ^ K ∧
          OutputsWithin MR (encodeInput I ++ encodeNat a) (encodeSecrets (reconstruct I a)) s) ∧
        ∀ y ∈ reconstruct I a, ((encodeNat y).length : ℝ) ≤ C * Real.log I.p ^ K) ∧
    (∀ p N X y : ℕ, p.Prime → 3 ≤ N → N < p → 1 ≤ X → X < p → y < p →
      prob (shifts p N y) (fun t => ∃ y' ∈ solutionSet (sampledInput p X N y t), y' ≠ y) ≤
        (4 : ℝ) ^ N * ((X : ℝ) - 1) ^ N / ((p : ℝ) - 1) ^ (N - 1)) := by sorry

end IntQuotHNP
