-- Prove2me | Theorems.Thm_FuchsThesis_Coding_eq_2_140
-- name    : FuchsThesis.Coding.eq_2_140
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:41.251827+00:00
-- url     : https://prove2.me/theorems/282611a0-c3d7-4bb2-90b9-0111aae0fb7c
-- title:
--   Eqs. (2.138)–(2.140) — every instantaneous code has $\bar l - H(p) \ge 0$
-- statement:
--   Let messages $x_1,\dots,x_n$ occur with probabilities $p(x_1),\dots,p(x_n)$, and let $c$ be any binary instantaneous (prefix-free) code for them, with codeword lengths $l(x_i)$. Then its expected length $\bar l = \sum_i p(x_i)\, l(x_i)$ is at least the Shannon information in bits:
--
--   $$
--   \bar l - H(p) \ge 0, \qquad H(p) = -\sum_i p(x_i)\log p(x_i).
--   $$
--
--   This is the lower half of Shannon's noiseless coding theorem (Theorem 2.8), stated for each code separately; taking the infimum over codes gives $H(p) \le \bar l_{\min}$.
--
--   Differences from the source:
--   - encoding: messages $x_1,\dots,x_n$ → an arbitrary finite type; reason: Lean convention, same instances up to relabelling.
--   - encoding: $\log$ to base 2 with $0\log 0 = 0$ → Mathlib's `Real.logb 2`, which has $\log_2 0 = 0$; reason: same values on every probability distribution.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (2.138)–(2.140), p.39 (PDF p.48)

import Mathlib
import Definitions.Def_FuchsThesis_Coding_IsInstantaneous
import Definitions.Def_FuchsThesis_Coding_expLength
import Definitions.Def_BBPSSW_Distill_shannonBits

namespace FuchsThesis.Coding

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eqs. (2.138)–(2.140), p.39 (PDF p.48): "for any instantaneous code"
for messages occurring with probabilities `p(xᵢ)`, the expected codeword length
`l̄ = ∑ᵢ p(xᵢ) l(xᵢ)` and the Shannon information in bits satisfy `l̄ − H(p) ≥ 0` (2.140).

**Formalization Note.** Messages form an arbitrary finite type `ι`; `p` is a probability
distribution (nonnegative, total mass one; zero probabilities allowed); `H(p)` is the published
`BBPSSW.Distill.shannonBits p = −∑ᵢ pᵢ log₂ pᵢ` (eq. (2.113) with `C = 1`, p.32; `0 log 0 = 0`). -/
theorem eq_2_140 {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (c : ι → List Bool) (hc : IsInstantaneous c) :
    expLength p c - BBPSSW.Distill.shannonBits p ≥ 0 := by sorry

end FuchsThesis.Coding
