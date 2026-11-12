-- Prove2me | Theorems.Thm_InteractionElim_Main_proposition_B_4_reliable
-- name    : InteractionElim.Main.proposition_B_4_reliable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:23:04.187928+00:00
-- url     : https://prove2.me/theorems/175cba76-7009-43d4-9071-5ed5fe21a984
-- title:
--   Proposition B.4 for reliable admissible protocols (corrected: the hypothesis 'reliable' is restored)
-- statement:
--   **Source** (Proposition B.4, p. 28): every admissible interactive protocol of worst-world fee $K$ satisfies $\gamma\sum_jF(W_j)\le AK$ for a universal constant $A$, under the regime (2.8).
--
--   **Variant:** there is a universal $A>0$ such that, for every workflow instance in (2.8), every **reliable** admissible protocol of worst-world fee $K$ satisfies $\gamma\sum_jF(W_j)\le AK$.
--
--   **Difference:** the variant adds the hypothesis "reliable" (failure probability at most $\delta$ in every world), which Propositions B.3 and B.6, the two cases of the printed proof, both assume; without it the always-guess protocol is a counterexample.
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 28, Proposition B.4 (corrected)

import Mathlib
import Definitions.Def_InteractionElim_Main_Protocol

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem proposition_B_4_reliable :
    ∃ A : ℝ, 0 < A ∧ ∀ I : Instance, I.Regime → ∀ pr : Protocol I, Reliable pr → Admissible pr →
      ENNReal.ofReal ((I.γ : ℝ) * I.Φ) ≤ ENNReal.ofReal A * fee pr := by sorry

end InteractionElim.Main
