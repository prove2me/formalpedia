-- Prove2me | Theorems.Thm_HypercliqueFalse_Supplement_theorem_1_2
-- name    : HypercliqueFalse.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:32:24.306076+00:00
-- url     : https://prove2.me/theorems/3c61ad8b-195e-4818-9576-6e7f1843878c
-- title:
--   Theorem 1.2 (k-AP Detection)
-- statement:
--   For every constant $k \ge 3$ there is a constant $\epsilon_k > 0$ such that a nontrivial $k$-term arithmetic progression in a given set $A \subseteq \{0, \dots, N\}$ can be detected in time
--   $$
--   O\big(N^{2-\epsilon_k}\big)
--   $$
--   on the word RAM with $\Theta(\log N)$-bit words.
--
--   For every $k \ge 4$ this refutes the $k$-AP Hypothesis of Dudek, Fischer, Gokaj, Jin, Künnemann, Mao and Redžić, which asserts that no $O(N^{2-\epsilon})$-time algorithm exists for any constant $\epsilon > 0$; consequently the problems shown hard under that hypothesis are open again.
--
--   **Formalization Note** The machine is the platform's published word RAM (`TrulySubcubicAPSP.Problem.SolvedInTime`): for every $\kappa$, one program correct at every word width $W \ge b(\lfloor\log_2 N\rfloor+1)$ on all inputs with integers at most $N^\kappa$, within $T(N) = O(N^r)$ steps. The quantifier order is $\forall k \ge 3\ \exists \epsilon_k$: the constant depends on $k$. The set is given as its $(N+1)$-cell indicator array.
--
--   Differences from the source:
--   - encoding: a constant ϵ_k > 0 (real) → ε : ℚ with 0 < ε; reason: the published BigO takes a rational exponent; a smaller ε only weakens the bound, so a real ε > 0 exists iff a rational one does
--   - encoding: a given set A ⊆ {0, …, N} → its 0-1 indicator array over {0, …, N} (N + 1 cells after the cell holding N); reason: a standard input representation of a subset of {0, …, N}, convertible from a list of its elements in O(N + |A|) time; it does not encode the answer
--   - encoding: word RAM with words of Θ(log N) bits (p.4) → the published SolvedInTime: one program correct at every width W ≥ b(⌊log₂ N⌋+1); reason: the published machine's convention for Θ(log n)-bit words, the same as the mission's goal; correctness at every larger width includes the Θ(log N) widths
--   - encoding: nontrivial k-AP (common difference d ≠ 0) → a, d ∈ ℕ with 0 < d and a + j·d ∈ A for all j < k; reason: a progression with negative difference is the same set read backwards, so the two conditions have the same instances
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Theorem 1.2, p.2 (PDF 3)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_HypercliqueFalse_Supplement_apDetection

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse.Supplement

/-- **Theorem 1.2 (k-AP Detection).** Fischer, *The Hyperclique Hypothesis is False*,
arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Theorem 1.2, p.2 (PDF 3): "For every
constant k ≥ 3, there is a constant ϵ_k > 0 such that a nontrivial k-AP in a given set
A ⊆ {0, . . . , N} can be detected in time O(N^{2−ϵ_k})."

On the published word RAM (`TrulySubcubicAPSP.Problem.SolvedInTime`: for every `κ`, one program
correct at every word width `W ≥ b(⌊log₂ N⌋ + 1)` on all inputs with integers at most `N^κ`, within
`T(N) = O(N^r)` steps), for the decision problem `apDetection k`, whose instance index is `N`.

**Formalization Note.** `∀ k ≥ 3, ∃ ε` (ε depends on `k`). `ε` is rational (the published `BigO`
takes a rational exponent; a smaller `ε` only weakens the bound, so this is equivalent to a real
`ε`). The input is the `(N + 1)`-cell 0-1 indicator array of `A`. -/
theorem theorem_1_2 : ∀ k : ℕ, 3 ≤ k → ∃ ε : ℚ, 0 < ε ∧
    (apDetection k).SolvedInTime (2 - ε) := by sorry

end HypercliqueFalse.Supplement
