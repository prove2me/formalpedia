-- Prove2me | Theorems.Thm_HypercliqueFalse_lemma_4_2
-- name    : HypercliqueFalse.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:31:50.359659+00:00
-- url     : https://prove2.me/theorems/0d904f43-bcb9-46dc-890e-4d2396f44698
-- title:
--   Lemma 4.2 (Rectangular Hyperclique)
-- statement:
--   Let $u \ge 2$ and $\epsilon > 0$ (in the paper $u = h-1$ with $h \ge 3$, and $\epsilon = \epsilon_{h-1}$). Assume that $H_u = H_{u+1,u}$ can be evaluated in time $O(n^{u+1-\epsilon})$. Then every instance of $H_u$ in which the $u+1$ variables range over $[n_0], \dots, [n_u]$ respectively can be evaluated in time
--   $$
--   O\!\left(\frac{n_0\cdot n_1\cdots n_u}{\min\{n_0,\dots,n_u\}^{\epsilon}}\right).
--   $$
--
--   Lemma 4.3 evaluates the inner sums of its three algorithms with this lemma.
--
--   Differences from the source:
--   - reading: word RAM with words of Θ(log n) bits, all integers polynomially bounded (p.4) → SolvedWithin: for every integer-bound exponent κ one program, correct at every word width W ≥ b(⌊log₂ s⌋+1) on every instance of scale s with integers at most s^κ, within C·bound + C steps, the bound in the instance's own dimensions (each at most s); reason: the paper runs subroutines on small blocks of a size-n instance with the size-n word RAM (Lemma 4.2, Lemma 4.3, proof of Theorem 2.1), so hypotheses and conclusions must cover instances smaller than the scale; at dimension = scale this is the plain statement, and every-width correctness is the published machine's convention for Θ(log n)-bit words (the paper's algorithms only add, subtract and multiply polynomially bounded integers)
--   - encoding: H_{h−1} with h ≥ 3 (Section 4), variables over [n₁], …, [n_h] → u = h − 1 with 2 ≤ u, variables x₀, …, x_u over [n₀], …, [n_u] (0-based); reason: renaming; same instances
--   - encoding: variables ranging over [n₁], …, [n_h] → sizes n_i = 0 allowed; reason: an empty range gives the empty sum; the bound is then 0 (Lean's 0/0 = 0) and the output cell already holds the value 0, so these instances cost only the additive constant
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.2, p.11

import Mathlib
import Definitions.Def_HypercliqueFalse_SolvedWithin
import Definitions.Def_HypercliqueFalse_hEval
import Definitions.Def_HypercliqueFalse_rectEval

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Lemma 4.2 (Rectangular Hyperclique).** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.2, p.11: "Assume
that H_{h−1} can be evaluated in time O(n^{h−ϵ_{h−1}}) for some ϵ_{h−1} > 0. Then every instance of
H_{h−1} in which the h variables range over [n₁], …, [n_h], respectively, can be evaluated in time
O(n₁ · … · n_h / min{n₁, …, n_h}^{ϵ_{h−1}})."

With `u = h − 1` (Section 4: `h ≥ 3`, so `u ≥ 2`): `H_u = H_{u+1,u}` is `hEval (u+1) u` and the
rectangular instances are `rectEval u` (`x.1 = (n₀, …, n_u)`).

**Formalization Note.** The minimum is `Finset.univ.inf'` over the `u + 1` sizes. -/
theorem lemma_4_2 (u : ℕ) (hu : 2 ≤ u) (ε : ℝ) (hε : 0 < ε)
    (hH : SolvedWithin (hEval (u + 1) u) (fun _ x => (x.1 : ℝ) ^ ((u : ℝ) + 1 - ε))) :
    SolvedWithin (rectEval u) (fun _ x =>
      (∏ i, (x.1 i : ℝ)) / ((Finset.univ.inf' Finset.univ_nonempty x.1 : ℕ) : ℝ) ^ ε) := by sorry

end HypercliqueFalse
