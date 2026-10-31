-- Prove2me | Theorems.Thm_FoundationsRL_DECExamples_proposition_15
-- name    : FoundationsRL.DECExamples.proposition_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:27.614123+00:00
-- url     : https://prove2.me/theorems/fc7bec15-c183-40ca-b953-9744597f1930
-- title:
--   Proposition 15 — DEC for the cheating code, $\mathrm{dec}_\gamma(\mathcal F)\lesssim\log_2(A)/\gamma$
-- statement:
--   Let $A=2^n$ and let $\mathcal F$ be the cheating code class of Example 4.2 on $\Pi=[A]\cup\{c_1,\dots,c_{\log_2 A}\}$. There is an absolute constant $C>0$ such that for every $n$ and every $\gamma>0$,
--
--   $$
--   \mathrm{dec}_\gamma(\mathcal F)=\sup_{\widehat f\in\mathrm{co}(\mathcal F)}\mathrm{dec}_\gamma(\mathcal F,\widehat f)\le C\,\frac{\log_2(A)}{\gamma}.
--   $$
--
--   Through the E2D regret bound (Proposition 13), this gives regret scaling with $\log_2 A$ rather than $\sqrt A$: the Decision-Estimation Coefficient adapts to the informative but unrewarding cheating actions that optimism and posterior sampling ignore.
--
--   The supremum is over the whole convex hull $\mathrm{co}(\mathcal F)$, as the proposition states; the printed proof treats only $\widehat f\in\mathcal F$ and notes that a similar strategy gives the same bound on $\mathrm{co}(\mathcal F)$.
--
--   **Formalization Note** $\log_2 A=n$. The constant $C$ is chosen before $n$ and $\gamma$. The decision space is finite, so $\Delta(\Pi)$ is all distributions on it.
--
--   Differences from the source:
--   - reading: π_f is "the action in [A] with highest reward" → any maximizer of f over [A] may be the encoded one; reason: the source is ambiguous under ties; this reading gives the larger class, and dec_γ is monotone in the class, so the bound for it implies the bound for every tie-breaking rule
--   - encoding: f(π_f) → sup over Π of f; reason: on this finite space the maximum is attained and the two agree
--   - encoding: Π = [A] ∪ C with A = 2ⁿ, log₂(A), 1-based indices → Fin (2ⁿ) ⊕ Fin n, n, 0-based indices; reason: Lean convention, same instances
--   - encoding: ≲ → an absolute constant C > 0 chosen before n and γ; reason: the meaning of ≲ in the notes
--   - reading: the function class F of Example 4.2, described by its properties → the set of all functions with those properties; reason: the example fixes no particular class; dec_γ is monotone in the class, so the bound for the largest one implies it for every class of the example
--   - encoding: min and max in (4.15), sup in (4.16) → ⨅ and ⨆ in EReal; reason: the max over F need not be attained; the decision space is finite, so the values agree
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 15, p. 69 (class defined in Example 4.2, pp. 62–63)

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_dec
import Definitions.Def_FoundationsRL_DECExamples_cheatingClass

namespace FoundationsRL.DECExamples

/-- **Proposition 15 (DEC for Cheating Code).** For the cheating code class,
`dec_γ(F) ≲ log₂(A) / γ`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Proposition 15, p. 69.

**Formalization Note.** `A = 2 ^ n`, so `log₂(A) = n`. `≲` is an absolute constant `C`, chosen before
`n` and `γ`. The supremum is over all of `co(F)`, as in (4.16); the printed proof treats only
`f̂ ∈ F`. -/
theorem proposition_15 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (γ : ℝ), 0 < γ →
      dec (cheatingClass n) γ ≤ ((C * n / γ : ℝ) : EReal) := by sorry

end FoundationsRL.DECExamples
