-- Prove2me | Theorems.Thm_OAI_Problem340_Construction_coverEntropy_realizedMap_eq_zero
-- name    : OAI.Problem340.Construction.coverEntropy_realizedMap_eq_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T23:13:19.53199+00:00
-- url     : https://prove2.me/theorems/179f61ba-4af4-4df9-8970-cbb0a033bc2b
-- title:
--   Proposition 4.3: the C¹ counterexample map has topological entropy zero (OpenAI entropy conjecture counterexample)
-- statement:
--   The paper's Proposition 4.3 ("The map $f$ defined in (10) has $h_{\mathrm{top}}(f) = 0$"), as OpenAI formalized it, for the map realized on the published manifold; an intermediate statement of the split of OpenAI's proof of `OAI.Problem340.exists_C1_entropy_counterexample` (the paper's Theorem 1.1).
--
--   **Notation** (published bundle `Def_C1EntropyCounterexample` and definitions bundle `OAIQWEC000` of this split). `CounterexampleManifold 3` is the unit circle in $\mathbb R^2$ times four copies of the unit sphere $S^2 \subset \mathbb R^3$. OpenAI's map lives on the model $\mathbb R/100\mathbb Z \times \Sigma \times \Sigma^3$, where $\Sigma = \mathbb C \cup \{\infty\}$ is the Riemann sphere (`OnePoint ℂ`): a clock coordinate $t$, a main coordinate $z$ that usually squares, and three registers (`rawMap`, the paper's map (10)). For $L > 2$, `concreteData L hL` fixes the paper's cutoffs, saturation and gain profile with parameter $L$, and `realizedMap L hL` is the resulting map transported to `CounterexampleManifold 3` by the homeomorphism `modelHomeomorph`.
--
--   **The statement.** For every real $L > 2$, the topological entropy of `realizedMap L hL` on the whole manifold, in Mathlib's cover formulation (`Dynamics.coverEntropy`), is $0$.
-- source:
--   OpenAI, A C^1 Counterexample to the Entropy Conjecture, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 151; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-C1-Counterexample-to-the-Entropy-Conjecture-September-25-2026/article.pdf, Proposition 4.3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/EntropyCounterexample/MapEntropyComplete.lean (declaration OAI.Problem340.Construction.coverEntropy_realizedMap_eq_zero)

import Mathlib
import Definitions.Def_C1EntropyCounterexample
import Definitions.Def_OAIQWEC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem coverEntropy_realizedMap_eq_zero (L : ℝ) (hL : 2 < L) :
    Dynamics.coverEntropy (realizedMap L hL)
      (Set.univ : Set (CounterexampleManifold 3)) = (0 : EReal) := by
  sorry

end Problem340.Construction

end

end OAI
end
