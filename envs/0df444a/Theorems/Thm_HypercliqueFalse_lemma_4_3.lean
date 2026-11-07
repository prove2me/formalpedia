-- Prove2me | Theorems.Thm_HypercliqueFalse_lemma_4_3
-- name    : HypercliqueFalse.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:33:11.430192+00:00
-- url     : https://prove2.me/theorems/b748accf-2ba2-4afb-80e4-a6e6385c78cc
-- title:
--   Lemma 4.3 (Base Case)
-- statement:
--   Let $h \ge 3$ and $0 < \epsilon \le \epsilon_2 = 3 - \log_2 7$ (Section 4's standing assumption on $\epsilon_{h-1}$). Assume that $H_{h-1} = H_{h,h-1}$ can be evaluated in time $O(n^{h-\epsilon})$. Then $T_h$ of size $(N, N, a, b, c)$ with $a, b, c \le N \le n$ can be evaluated in time
--   $$
--   O\big(N^4\, n^{h-3}\,(abc)^{1-\delta}\big), \qquad \delta = \epsilon^2/8 .
--   $$
--
--   These are the leaves of the recursion in the proof of Theorem 2.1.
--
--   **Formalization Note** The upper bound $\epsilon \le \epsilon_2$ is not in the sentence of Lemma 4.3 but is the standing assumption of Section 4 ("assume that $H_{h-1}$ can be evaluated in time $O(n^{h-\epsilon_{h-1}})$ for some constant $0<\epsilon_{h-1}\le\epsilon_2$", p.9), used in the proof ("as we are assuming $\epsilon_{h-1}\le\epsilon_2$", p.12).
--
--   Differences from the source:
--   - reading: word RAM with words of Θ(log n) bits, all integers polynomially bounded (p.4) → SolvedWithin: for every integer-bound exponent κ one program, correct at every word width W ≥ b(⌊log₂ s⌋+1) on every instance of scale s with integers at most s^κ, within C·bound + C steps, the bound in the instance's own dimensions (each at most s); reason: the paper runs subroutines on small blocks of a size-n instance with the size-n word RAM (Lemma 4.2, Lemma 4.3, proof of Theorem 2.1), so hypotheses and conclusions must cover instances smaller than the scale; at dimension = scale this is the plain statement, and every-width correctness is the published machine's convention for Θ(log n)-bit words (the paper's algorithms only add, subtract and multiply polynomially bounded integers)
--   - encoding: T_h of size (N, N, a, b, c) with a, b, c ≤ N ≤ n → a, b, c = 0 allowed; reason: an empty index range gives T_h = 0; the bound is then 0 (the exponent 1 − ε²/8 is nonzero) and the output cell already holds the value 0, so these instances cost only the additive constant
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.3, p.11; standing assumption of Section 4, p.9; proof, pp.11–12

import Mathlib
import Definitions.Def_HypercliqueFalse_SolvedWithin
import Definitions.Def_HypercliqueFalse_hEval
import Definitions.Def_HypercliqueFalse_tEval

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Lemma 4.3 (Base Case).** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.3, p.11: "Assume that H_{h−1} can be
evaluated in time O(n^{h−ϵ_{h−1}}) for some ϵ_{h−1} > 0. Then T_h of size (N, N, a, b, c) with
a, b, c ≤ N ≤ n can be evaluated in time O(N⁴n^{h−3}(abc)^{1−δ}) for δ = ϵ²_{h−1}/8."

Under Section 4's standing assumption (p.9: "let h ≥ 3, and assume that H_{h−1} can be evaluated in
time O(n^{h−ϵ_{h−1}}) for some constant 0 < ϵ_{h−1} ≤ ϵ₂", used on p.12: "as we are assuming
ϵ_{h−1} ≤ ϵ₂"), with `ϵ₂ = 3 − log₂ 7`.

**Formalization Note.** An instance of `tEval h` is `⟨n, N, a, b, c, _, T⟩`; the bound is
`N⁴ · n^{h−3} · (abc)^{1−ε²/8}`. `H_{h−1} = H_{h,h−1}` is `hEval h (h − 1)`. -/
theorem lemma_4_3 (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) (hε₂ : ε ≤ 3 - Real.logb 2 7)
    (hH : SolvedWithin (hEval h (h - 1)) (fun _ x => (x.1 : ℝ) ^ ((h : ℝ) - ε))) :
    SolvedWithin (tEval h) (fun _ x =>
      (x.2.1 : ℝ) ^ 4 * (x.1 : ℝ) ^ (h - 3) *
        ((x.2.2.1 : ℝ) * x.2.2.2.1 * x.2.2.2.2.1) ^ (1 - ε ^ 2 / 8)) := by sorry

end HypercliqueFalse
