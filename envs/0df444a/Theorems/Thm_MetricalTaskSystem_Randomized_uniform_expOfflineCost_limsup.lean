-- Prove2me | Theorems.Thm_MetricalTaskSystem_Randomized_uniform_expOfflineCost_limsup
-- name    : MetricalTaskSystem.Randomized.uniform_expOfflineCost_limsup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:21:03.917987+00:00
-- url     : https://prove2.me/theorems/98b0413a-4692-46a5-93c8-fe0129506226
-- title:
--   Section 7, lower bound — the expected off-line cost is at most $j/(nH(n)) + O(1)$
-- statement:
--   Let $(S,d)$ be the uniform task system on $n$ states, let the tasks be independent and uniformly distributed unit elementary tasks, and let $s_0$ be an initial state. Then there is a constant $C$, independent of $j$, such that for every $j \ge 0$
--   $$E\big(c_0(\mathbf T^j)\big)\le\frac{j}{nH(n)}+C .$$
--
--   This is the denominator estimate in the application of Lemma 7.2: together with $m_j\ge j/n$ it gives $\limsup_j m_j/E(c_0(\mathbf T^j))\ge H(n)$.
--
--   **Formalization Note** The paper's $O(1)$ is rendered as an explicit existential constant $C$ chosen after the system and the initial state and before $j$. The paper's own justification (the elementary renewal theorem) gives only the limit of $E(c_j)/j$; the additive bound as stated needs a sharper renewal estimate, which is a proof cost, not a change of statement.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 760, Section 7, proof of Theorem 7.1 (lower bound), off-line strategy and renewal argument

import Mathlib
import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_TaskDistribution

namespace MetricalTaskSystem.Randomized

/-- **Section 7, proof of the lower bound, off-line cost** (Borodin–Linial–Saks 1992, p. 760).
On the uniform task system with `n = |S|` states and independent uniformly distributed unit
elementary tasks, `E(c₀(Tʲ)) ≤ j/(n·H(n)) + O(1)`: there is a constant `C` (depending on the
system and the initial state, not on `j`) with `E(c₀(Tʲ)) ≤ j/(n·H(n)) + C` for every `j`. -/
theorem uniform_expOfflineCost_limsup {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (s₀ : S) :
    ∃ C : ℝ, ∀ j : ℕ,
      expOfflineCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j ≤
        (j : ℝ) / ((Fintype.card S : ℝ) * (harmonic (Fintype.card S) : ℝ)) + C := by sorry

end MetricalTaskSystem.Randomized
