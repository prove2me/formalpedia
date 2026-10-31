-- Prove2me | Theorems.Thm_FuchsThesis_Coding_lemma_2_3_existence
-- name    : FuchsThesis.Coding.lemma_2_3_existence
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:40.775636+00:00
-- url     : https://prove2.me/theorems/6350bb60-9275-4c9e-bd7d-bfd3ee51ce94
-- title:
--   Lemma 2.3 (Kraft), second statement — lengths satisfying $\sum_i 2^{-k_i}\le 1$ are realized by an instantaneous code
-- statement:
--   Let $x_1,\dots,x_n$ be messages and let $k_1,\dots,k_n$ be integers satisfying the Kraft inequality
--
--   $$
--   \sum_{i=1}^{n} 2^{-k_i} \le 1 .
--   $$
--
--   Then there is a binary instantaneous (prefix-free) code for $x_1,\dots,x_n$ whose codeword for $x_i$ has length exactly $k_i$, for every $i$.
--
--   Together with the first statement of Lemma 2.3 (every instantaneous code satisfies the Kraft inequality), this characterizes the length profiles of instantaneous codes. It is what turns the lengths $\lceil -\log p(x_i)\rceil$ of (2.141) into an actual code in the proof of the upper bound of Theorem 2.8.
--
--   Note that the inequality forces every $k_i \ge 0$ (a single term with $k_i < 0$ already exceeds $1$), and $k_i = 0$ is possible only for a single message, whose codeword is then empty.
--
--   Differences from the source:
--   - generalization: integers listed in increasing order $k_1 \le \dots \le k_n$ → any family of integers indexed by the messages, in no order; reason: the order is only a labelling, and every family can be relabelled increasingly, so the statement specializes to the source's.
--   - encoding: messages $\{x_1,\dots,x_n\}$ → an arbitrary finite type; reason: Lean convention, every finite type is a relabelling of $\{1,\dots,n\}$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Lemma 2.3 (Kraft), second statement, p.37 (PDF p.46); proof on p.39 (PDF p.48)

import Mathlib
import Definitions.Def_FuchsThesis_Coding_IsInstantaneous

namespace FuchsThesis.Coding

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Lemma 2.3 (Kraft), second statement, p.37 (PDF p.46): "for any set of
integers `k₁ ≤ k₂ ≤ ⋯ ≤ kₙ` satisfying this inequality [`∑ 2^{−kᵢ} ≤ 1`, (2.134)], there exists a
instantaneous code with these as codeword lengths."

**Formalization Note.** The messages form an arbitrary finite type `ι` and the integers are a
family `k : ι → ℤ`; no ordering is imposed (the source's `k₁ ≤ ⋯ ≤ kₙ` is a labelling, and every
family can be relabelled in increasing order). The Kraft sum is taken in `ℝ` with integer powers
`2 ^ (−kᵢ)`. Negative integers are not excluded by hypothesis: a single term with `kᵢ < 0` already
exceeds `1`. A zero length is allowed (the empty codeword, possible only when `ι` has one
element). -/
theorem lemma_2_3_existence {ι : Type*} [Fintype ι] (k : ι → ℤ)
    (hK : ∑ i, (2 : ℝ) ^ (-(k i)) ≤ 1) :
    ∃ c : ι → List Bool, IsInstantaneous c ∧ ∀ i, ((c i).length : ℤ) = k i := by sorry

end FuchsThesis.Coding
