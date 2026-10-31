-- Prove2me | Theorems.Thm_FuchsThesis_Coding_theorem_2_8
-- name    : FuchsThesis.Coding.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:27.037978+00:00
-- url     : https://prove2.me/theorems/36c035c3-2e27-4006-a58d-640f86b47cae
-- title:
--   Theorem 2.8 (Shannon's noiseless coding theorem) — $H(p) \le \bar l_{\min} \le H(p)+1$
-- statement:
--   Suppose messages $x_1,\dots,x_n$ occur with probabilities $p(x_1),\dots,p(x_n)$ (nonnegative, summing to one; zero probabilities are allowed). Let $\bar l_{\min}$ be the minimal average codeword length
--
--   $$
--   \bar l_{\min} = \inf_{c} \sum_i p(x_i)\, l(x_i)
--   $$
--
--   over all binary instantaneous (prefix-free) codes $c$ for these messages, where $l(x_i)$ is the length of the codeword of $x_i$. Then
--
--   $$
--   H(p) \;\le\; \bar l_{\min} \;\le\; H(p) + 1 ,
--   $$
--
--   where $H(p) = -\sum_i p(x_i)\log p(x_i)$ is the Shannon information of $p$ measured in bits ($\log$ to base 2, $0\log 0 = 0$).
--
--   In the language of questioning schemes, the least expected number of yes/no questions needed to identify the outcome of sampling $p$ lies within one question of $H(p)$. This gives the Shannon information an operational meaning, and applied to blocks of $N$ independent samples it shows that the number of questions per sample can be brought as close to $H(p)$ as desired.
--
--   Differences from the source:
--   - encoding: messages $x_1,\dots,x_n$ → an arbitrary finite type (nonempty because the probabilities sum to one); reason: Lean convention, same instances up to relabelling.
--   - encoding: the "minimal" average codeword length → the infimum (`sInf`) of the expected lengths of all instantaneous codes; reason: the set is nonempty and bounded below by 0 (proved in the sanity file) and its minimum is attained, so infimum and minimum agree.
--   - encoding: $\log$ to base 2 with $0 \log 0 = 0$ → Mathlib's `Real.logb 2`, which has $\log_2 0 = 0$; reason: same values on every probability distribution.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.8 (Shannon), eq. (2.137), p.39 (PDF p.48)

import Mathlib
import Definitions.Def_FuchsThesis_Coding_minLength
import Definitions.Def_BBPSSW_Distill_shannonBits

namespace FuchsThesis.Coding

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.8 (Shannon), eq. (2.137), p.39 (PDF p.48): "Suppose messages
`x₁, …, xₙ` occur with probabilities `p(x₁), …, p(xₙ)`. Then the minimal average codeword length
`l̄_min` for a binary instantaneous coding of these messages satisfies
`H(p) ≤ l̄_min ≤ H(p) + 1`, where `H(p)` is the Shannon information of the distribution `p(xᵢ)`
measured in bits."

**Formalization Note.** Messages form an arbitrary finite type `ι` (nonempty, since the
probabilities sum to one); `p` is any probability distribution, zero probabilities included.
`l̄_min` is `minLength p`, the infimum of `∑ᵢ p(xᵢ) l(xᵢ)` over all binary instantaneous
(prefix-free) codes; `H(p)` is the published `BBPSSW.Distill.shannonBits p = −∑ᵢ pᵢ log₂ pᵢ`
(eq. (2.113) with `C = 1`, p.32; `Real.logb 2 0 = 0` gives `0 log 0 = 0`). The upper bound is the source's non-strict one: with zero probabilities it can be attained (e.g. `p = (1, 0)`, where
`H(p) = 0` and every instantaneous code gives the first message a nonempty codeword). -/
theorem theorem_2_8 {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    BBPSSW.Distill.shannonBits p ≤ minLength p ∧ minLength p ≤ BBPSSW.Distill.shannonBits p + 1 := by sorry

end FuchsThesis.Coding
