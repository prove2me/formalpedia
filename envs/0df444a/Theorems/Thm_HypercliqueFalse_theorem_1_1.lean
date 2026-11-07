-- Prove2me | Theorems.Thm_HypercliqueFalse_theorem_1_1
-- name    : HypercliqueFalse.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:33:10.300719+00:00
-- url     : https://prove2.me/theorems/6532ad9e-aed5-46ec-b660-833d5f73100b
-- title:
--   Theorem 1.1 (Hyperclique Detection)
-- statement:
--   For every constant $h \ge 2$ there is a constant $\epsilon_h > 0$ such that, for every constant $k > h$, a $k$-hyperclique in an $h$-uniform hypergraph with $n$ vertices can be detected in time
--   $$
--   O\big(n^{(1-\epsilon_h)k}\big)
--   $$
--   on the word RAM with $\Theta(\log n)$-bit words.
--
--   For $h \ge 3$ this refutes the Hyperclique Hypothesis of Lincoln, Vassilevska Williams and Williams, which asserts that time $n^{k-o(1)}$ is necessary for all constants $k > h \ge 3$.
--
--   **Formalization Note** The machine is the platform's published word RAM (`TrulySubcubicAPSP.Problem.SolvedInTime`): for every $\kappa$, one program correct at every word width $W \ge b(\lfloor\log_2 n\rfloor+1)$ on all inputs with integers at most $n^\kappa$, within $T(n) = O(n^r)$ steps. The hypergraph is given as its $n^h$-cell indicator array.
--
--   Differences from the source:
--   - encoding: a constant ϵ_h > 0 (real) → ε : ℚ with 0 < ε; reason: the published BigO takes a rational exponent; a smaller ε only weakens the bound, so a real ε > 0 exists iff a rational one does
--   - encoding: an h-uniform hypergraph with n vertices → its 0-1 indicator array over [n]^h (n^h cells after the cell holding n); reason: a standard input representation; it does not encode the answer
--   - encoding: word RAM with words of Θ(log n) bits (p.4) → the published SolvedInTime: one program correct at every width W ≥ b(⌊log₂ n⌋+1); reason: the published machine's convention for Θ(log n)-bit words, shared with the platform's 3SUM and APSP refutations; correctness at every larger width includes the Θ(log n) widths, and the paper's algorithms only add, subtract and multiply polynomially bounded integers (p.4)
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Theorem 1.1, p.1

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_HypercliqueFalse_hypercliqueDetection

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse

/-- **Theorem 1.1 (Hyperclique Detection).** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Theorem 1.1, p.1: "For every
constant h ≥ 2, there is a constant ϵ_h > 0 such that, for every constant k > h, a k-clique in an
h-uniform hypergraph with n vertices can be detected in time O(n^{(1−ϵ_h)k})."

On the published word RAM (`TrulySubcubicAPSP.Problem.SolvedInTime`: for every `κ`, one program
correct at every word width `W ≥ b(⌊log₂ n⌋ + 1)` on all inputs with integers at most `n^κ`, within
`T(n) = O(n^r)` steps), for the decision problem `hypercliqueDetection k h`.

**Formalization Note.** `∀ h ∃ ε ∀ k`. `ε` is rational (the published `BigO` takes a rational
exponent; a smaller `ε` only weakens the bound, so this is equivalent to a real `ε`). The input is
the `n^h`-cell 0-1 indicator array of the hyperedges. -/
theorem theorem_1_1 : ∀ h : ℕ, 2 ≤ h → ∃ ε : ℚ, 0 < ε ∧ ∀ k : ℕ, h < k →
    (hypercliqueDetection k h).SolvedInTime ((1 - ε) * k) := by sorry

end HypercliqueFalse
