-- Prove2me | Theorems.Thm_HypercliqueFalse_base_case_h2
-- name    : HypercliqueFalse.base_case_h2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:31:44.482495+00:00
-- url     : https://prove2.me/theorems/c317a3fa-e4d4-4ba0-a40e-accea644a86e
-- title:
--   Section 4 — base case $h=2$: $H_2$ in time $O(n^{3-\epsilon_2})$, $\epsilon_2 = 3-\log_2 7 > 0$
-- statement:
--   Let $\epsilon_2 := 3 - \log_2 7$. Then $\epsilon_2 > 0$, and the hyperclique polynomial
--   $$
--   H_2 = H_{3,2} = \sum_{x_1, x_2, x_3 \in [n]} A_{x_2x_3}\,B_{x_1x_3}\,C_{x_1x_2}
--   $$
--   can be evaluated in time $O(n^{3-\epsilon_2}) = O(n^{\log_2 7})$ (for $h = 2$ the problem is one matrix product, computed with Strassen's algorithm).
--
--   This is the base case of the induction on $h$ in the proof of Theorem 2.1, and $\epsilon_2$ caps the savings assumed in Section 4.
--
--   Differences from the source:
--   - reading: word RAM with words of Θ(log n) bits, all integers polynomially bounded (p.4) → SolvedWithin: for every integer-bound exponent κ one program, correct at every word width W ≥ b(⌊log₂ s⌋+1) on every instance of scale s with integers at most s^κ, within C·bound + C steps, the bound in the instance's own dimensions (each at most s); reason: the paper runs subroutines on small blocks of a size-n instance with the size-n word RAM (Lemma 4.2, Lemma 4.3, proof of Theorem 2.1), so hypotheses and conclusions must cover instances smaller than the scale; at dimension = scale this is the plain statement, and every-width correctness is the published machine's convention for Θ(log n)-bit words (the paper's algorithms only add, subtract and multiply polynomially bounded integers)
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 4, p.9; proof of Theorem 2.1, p.13

import Mathlib
import Definitions.Def_HypercliqueFalse_SolvedWithin
import Definitions.Def_HypercliqueFalse_hEval

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Base case `h = 2`: `H₂` in time `O(n^{3−ϵ₂})` for `ϵ₂ = 3 − log₂ 7 > 0`.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730),
Section 4, p.9: "In the base case, for h = 2, the problem degenerates to matrix multiplication, so
that, using Strassen's algorithm, H₂ can be evaluated in time O(n^{3−ϵ₂}) for ϵ₂ := 3 − log₂ 7 > 0";
proof of Theorem 2.1, p.13.

`H₂ = H_{3,2}` is `hEval 3 2`; the time bound is in the instance's size `m = x.1`. -/
theorem base_case_h2 :
    0 < 3 - Real.logb 2 7 ∧
      SolvedWithin (hEval 3 2) (fun _ x => (x.1 : ℝ) ^ ((3 : ℝ) - (3 - Real.logb 2 7))) := by sorry

end HypercliqueFalse
