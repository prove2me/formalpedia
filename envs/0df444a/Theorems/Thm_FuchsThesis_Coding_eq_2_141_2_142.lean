-- Prove2me | Theorems.Thm_FuchsThesis_Coding_eq_2_141_2_142
-- name    : FuchsThesis.Coding.eq_2_141_2_142
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:14.26242+00:00
-- url     : https://prove2.me/theorems/f2f4b23e-facc-4c7d-b561-f45eee731f47
-- title:
--   Eqs. (2.141)–(2.142) — the lengths $\lceil -\log p(x_i)\rceil$ give an instantaneous code and $\bar l_{\min} \le H(p)+1$
-- statement:
--   Let messages $x_1,\dots,x_n$ occur with probabilities $p(x_1),\dots,p(x_n)$, all strictly positive. Then:
--
--   1. there is a binary instantaneous code whose codeword for $x_i$ has length $l(x_i) = \lceil -\log p(x_i) \rceil$ for every $i$ (2.141);
--   2. the minimal average codeword length satisfies
--   $$
--   \bar l_{\min} \;\le\; \sum_i p(x_i)\,\lceil -\log p(x_i)\rceil \;\le\; \sum_i p(x_i)\,(-\log p(x_i) + 1) \;=\; H(p) + 1 \qquad (2.142).
--   $$
--
--   Here $\log$ is the base-2 logarithm, $\lceil x\rceil$ is the smallest integer $\ge x$, and $H(p) = -\sum_i p(x_i)\log p(x_i)$ is the Shannon information in bits. The lengths in (2.141) are those of the Shannon code; they satisfy the Kraft inequality, which is why the code exists. This is the upper half of Shannon's noiseless coding theorem for distributions without zero probabilities.
--
--   Differences from the source:
--   - encoding: lengths $\lceil -\log p(x_i)\rceil$ for messages with probabilities $p(x_i)$ → the hypothesis $p(x_i) > 0$ for all $i$; reason: $\lceil -\log 0\rceil$ is undefined, so the hypothesis excludes exactly the messages for which (2.141) has no meaning; the goal theorem covers zero probabilities.
--   - encoding: messages $x_1,\dots,x_n$ → an arbitrary finite type, $\lceil\cdot\rceil$ → `Int.ceil` cast to $\mathbb R$, $\log$ → `Real.logb 2`; reason: Lean conventions, same values.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (2.141)–(2.142), p.39 (PDF p.48)

import Mathlib
import Definitions.Def_FuchsThesis_Coding_IsInstantaneous
import Definitions.Def_FuchsThesis_Coding_expLength
import Definitions.Def_FuchsThesis_Coding_minLength
import Definitions.Def_BBPSSW_Distill_shannonBits

namespace FuchsThesis.Coding

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eqs. (2.141)–(2.142), p.39 (PDF p.48): "there is an instantaneous code
with codeword lengths given by `l(xᵢ) = ⌈−log p(xᵢ)⌉` (2.141) … because these integers satisfy the
Kraft inequality. Therefore it must hold that
`l̄_min ≤ ∑ᵢ p(xᵢ)⌈−log p(xᵢ)⌉ ≤ ∑ᵢ p(xᵢ)(−log p(xᵢ) + 1) = H(p) + 1` (2.142)."

**Formalization Note.** Messages form an arbitrary finite type `ι`; `log` is `Real.logb 2` and
`⌈·⌉` is `Int.ceil`. The hypothesis `hpos : ∀ i, 0 < p i` excludes exactly the messages for which
`⌈−log p(xᵢ)⌉` in (2.141) is undefined (`p(xᵢ) = 0`); the theorem `theorem_2_8` itself allows
zero probabilities. The conclusion has four parts: the code of (2.141) exists, and the two
inequalities and the final equality of the chain (2.142), with `H(p)` the published
`BBPSSW.Distill.shannonBits p = −∑ᵢ pᵢ log₂ pᵢ`. -/
theorem eq_2_141_2_142 {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hpos : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) :
    (∃ c : ι → List Bool, IsInstantaneous c ∧
        ∀ i, ((c i).length : ℤ) = ⌈-Real.logb 2 (p i)⌉) ∧
      minLength p ≤ ∑ i, p i * (⌈-Real.logb 2 (p i)⌉ : ℝ) ∧
      ∑ i, p i * (⌈-Real.logb 2 (p i)⌉ : ℝ) ≤ ∑ i, p i * (-Real.logb 2 (p i) + 1) ∧
      ∑ i, p i * (-Real.logb 2 (p i) + 1) = BBPSSW.Distill.shannonBits p + 1 := by sorry

end FuchsThesis.Coding
