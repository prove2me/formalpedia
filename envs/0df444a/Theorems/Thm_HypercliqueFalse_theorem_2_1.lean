-- Prove2me | Theorems.Thm_HypercliqueFalse_theorem_2_1
-- name    : HypercliqueFalse.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:31:51.928228+00:00
-- url     : https://prove2.me/theorems/ca20cadc-208e-4ce6-82d1-8e3f72aa4f63
-- title:
--   Theorem 2.1 — $H_{k,h}$ can be evaluated in time $O(n^{(1-\epsilon_h)k})$
-- statement:
--   For every constant $h \ge 2$ there is a constant $\epsilon_h > 0$ such that, for every constant $k > h$, the $(k,h)$-hyperclique polynomial $H_{k,h}$ can be evaluated in time
--   $$
--   O\big(n^{(1-\epsilon_h)k}\big).
--   $$
--
--   The quantifiers are in the order $\forall h\ \exists \epsilon_h\ \forall k$: the saving depends on $h$ only. With the counting identity this gives Theorem 1.1.
--
--   Differences from the source:
--   - reading: word RAM with words of Θ(log n) bits, all integers polynomially bounded (p.4) → SolvedWithin: for every integer-bound exponent κ one program, correct at every word width W ≥ b(⌊log₂ s⌋+1) on every instance of scale s with integers at most s^κ, within C·bound + C steps, the bound in the instance's own dimensions (each at most s); reason: the paper runs subroutines on small blocks of a size-n instance with the size-n word RAM (Lemma 4.2, Lemma 4.3, proof of Theorem 2.1), so hypotheses and conclusions must cover instances smaller than the scale; at dimension = scale this is the plain statement, and every-width correctness is the published machine's convention for Θ(log n)-bit words (the paper's algorithms only add, subtract and multiply polynomially bounded integers)
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Theorem 2.1, p.4

import Mathlib
import Definitions.Def_HypercliqueFalse_SolvedWithin
import Definitions.Def_HypercliqueFalse_hEval

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Theorem 2.1.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Theorem 2.1, p.4: "For every constant h ≥ 2, there is
a constant ϵ_h > 0 such that, for every constant k > h, the polynomial H_{k,h} can be evaluated in
time O(n^{(1−ϵ_h)k})."

**Formalization Note.** `∀ h ∃ ε ∀ k`: `ε` depends on `h` only; the program may depend on `h` and
`k`. The time bound is in the instance's size `m = x.1` at any scale `s ≥ m` (`SolvedWithin`). -/
theorem theorem_2_1 : ∀ h : ℕ, 2 ≤ h → ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, h < k →
    SolvedWithin (hEval k h) (fun _ x => (x.1 : ℝ) ^ ((1 - ε) * k)) := by sorry

end HypercliqueFalse
