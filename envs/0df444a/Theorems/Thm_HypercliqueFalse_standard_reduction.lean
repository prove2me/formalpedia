-- Prove2me | Theorems.Thm_HypercliqueFalse_standard_reduction
-- name    : HypercliqueFalse.standard_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:08.007196+00:00
-- url     : https://prove2.me/theorems/e14ba9ce-a40c-4564-8406-c8a3de413318
-- title:
--   Section 2 — the standard reduction to $k=h+1$
-- statement:
--   Let $h \ge 2$ and $\epsilon > 0$. Assume that $H_{h+1,h}$ can be evaluated in time $O(n^{h+1-\epsilon})$. Then for every $k > h$, the polynomial $H_{k,h}$ can be evaluated in time
--   $$
--   O\big(n^{\,k - \epsilon\lfloor k/(h+1)\rfloor}\big),
--   $$
--   by brute force over $k \bmod (h+1)$ of the variables and grouping the remaining variables into $h+1$ blocks of $\lfloor k/(h+1)\rfloor$ variables. When $h + 1$ divides $k$ this is the bound $O(n^{(1-\epsilon/(h+1))k})$ of the paper.
--
--   With the inductive step and the base case this gives Theorem 2.1, since $\lfloor k/(h+1)\rfloor \ge k/(2(h+1))$ for $k \ge h+1$.
--
--   **Formalization Note** $\lfloor k/(h+1)\rfloor$ is natural-number division.
--
--   Differences from the source:
--   - generalization: O(n^{(1−ϵ/(h+1))k}), stated under "Assume that h + 1 divides k" (otherwise brute force over k mod (h + 1) variables) → every k > h, time O(n^{k − ε⌊k/(h+1)⌋}); reason: this is what the described reduction gives for every k; it equals the printed exponent when h + 1 divides k
--   - reading: word RAM with words of Θ(log n) bits, all integers polynomially bounded (p.4) → SolvedWithin: for every integer-bound exponent κ one program, correct at every word width W ≥ b(⌊log₂ s⌋+1) on every instance of scale s with integers at most s^κ, within C·bound + C steps, the bound in the instance's own dimensions (each at most s); reason: the paper runs subroutines on small blocks of a size-n instance with the size-n word RAM (Lemma 4.2, Lemma 4.3, proof of Theorem 2.1), so hypotheses and conclusions must cover instances smaller than the scale; at dimension = scale this is the plain statement, and every-width correctness is the published machine's convention for Θ(log n)-bit words (the paper's algorithms only add, subtract and multiply polynomially bounded integers)
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, p.4

import Mathlib
import Definitions.Def_HypercliqueFalse_SolvedWithin
import Definitions.Def_HypercliqueFalse_hEval

set_option autoImplicit false

namespace HypercliqueFalse

/-- **The standard reduction to `k = h + 1`.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, p.4: "By the
following standard reduction [NP85], it suffices to consider the case k = h + 1. Assume that h + 1
divides k (otherwise, we first brute-force over k mod(h + 1) of the variables). … This is an
instance of H_{h+1,h} with n^{k/(h+1)} in place of n. Thus, an O(n^{h+1−ϵ})-time algorithm for
H_{h+1,h} evaluates H_{k,h} in time O(n^{(1−ϵ/(h+1))k})."

For every `k > h`, with `k mod (h + 1)` variables brute-forced and `⌊k/(h+1)⌋`-variable blocks: time
`O(n^{k − ϵ⌊k/(h+1)⌋})`, which is the printed `O(n^{(1−ϵ/(h+1))k})` when `h + 1` divides `k`.

**Formalization Note.** `k / (h + 1)` is natural-number division (the floor). -/
theorem standard_reduction (h : ℕ) (hh : 2 ≤ h) (ε : ℝ) (hε : 0 < ε)
    (hH : SolvedWithin (hEval (h + 1) h) (fun _ x => (x.1 : ℝ) ^ ((h : ℝ) + 1 - ε)))
    (k : ℕ) (hk : h < k) :
    SolvedWithin (hEval k h) (fun _ x => (x.1 : ℝ) ^ ((k : ℝ) - ε * ((k / (h + 1) : ℕ) : ℝ))) := by sorry

end HypercliqueFalse
