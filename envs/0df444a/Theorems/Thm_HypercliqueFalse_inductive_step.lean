-- Prove2me | Theorems.Thm_HypercliqueFalse_inductive_step
-- name    : HypercliqueFalse.inductive_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:31:48.639136+00:00
-- url     : https://prove2.me/theorems/e0c868a8-c827-4041-9ef4-d23f0f2c5338
-- title:
--   Proof of Theorem 2.1 — the inductive step: $H_h$ in time $O(n^{h+1-\epsilon_h})$, $\epsilon_h = \delta^2/(12\log_2(1/\delta))$
-- statement:
--   Let $h \ge 3$ and $0 < \epsilon \le \epsilon_2 = 3 - \log_2 7$ (Section 4's standing assumption on $\epsilon_{h-1}$). Assume that $H_{h-1} = H_{h,h-1}$ can be evaluated in time $O(n^{h-\epsilon})$. Let $\delta = \epsilon^2/8$. Then $H_h = H_{h+1,h}$ can be evaluated in time
--   $$
--   O\big(n^{h+1-\epsilon_h}\big), \qquad \epsilon_h = \frac{\delta^2}{12\log_2(1/\delta)} > 0 .
--   $$
--
--   This is the inductive step of the proof of Theorem 2.1: the recursion of Lemma 4.1 for $2L$ levels, the leaves evaluated by Lemma 4.3, the cost bounded with the potential calculation and the choice of $q$.
--
--   Differences from the source:
--   - reading: word RAM with words of Θ(log n) bits, all integers polynomially bounded (p.4) → SolvedWithin: for every integer-bound exponent κ one program, correct at every word width W ≥ b(⌊log₂ s⌋+1) on every instance of scale s with integers at most s^κ, within C·bound + C steps, the bound in the instance's own dimensions (each at most s); reason: the paper runs subroutines on small blocks of a size-n instance with the size-n word RAM (Lemma 4.2, Lemma 4.3, proof of Theorem 2.1), so hypotheses and conclusions must cover instances smaller than the scale; at dimension = scale this is the plain statement, and every-width correctness is the published machine's convention for Θ(log n)-bit words (the paper's algorithms only add, subtract and multiply polynomially bounded integers)
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Theorem 2.1, p.13; standing assumption of Section 4, p.9

import Mathlib
import Definitions.Def_HypercliqueFalse_SolvedWithin
import Definitions.Def_HypercliqueFalse_hEval

set_option autoImplicit false

namespace HypercliqueFalse

/-- **The inductive step of Theorem 2.1.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Theorem 2.1, p.13:
"Next, focus on the inductive step for h ≥ 3, i.e., assume that H_{h−1} can be evaluated in time
O(n^{h−ϵ_{h−1}}) by the induction hypothesis; we give an algorithm to evaluate H_h. Let δ = ϵ²_{h−1}/8
… Hence, H_h can be evaluated in time O(n^{h+1−ϵ} log n) = O(n^{h+1−ϵ_h}) for
ϵ_h = δ²/(12 log₂(1/δ)) > 0."

Under Section 4's standing assumption `0 < ϵ_{h−1} ≤ ϵ₂ = 3 − log₂ 7` (p.9). `H_{h−1}` is
`hEval h (h − 1)` and `H_h = H_{h+1,h}` is `hEval (h + 1) h`; `δ = ε²/8` is written out. -/
theorem inductive_step (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) (hε₂ : ε ≤ 3 - Real.logb 2 7)
    (hH : SolvedWithin (hEval h (h - 1)) (fun _ x => (x.1 : ℝ) ^ ((h : ℝ) - ε))) :
    SolvedWithin (hEval (h + 1) h) (fun _ x => (x.1 : ℝ) ^
      ((h : ℝ) + 1 - (ε ^ 2 / 8) ^ 2 / (12 * Real.logb 2 (1 / (ε ^ 2 / 8))))) := by sorry

end HypercliqueFalse
