-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_haarReplicaBlock
-- name    : OAI.PosteriorReplicas.haarReplicaBlock
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:31:47.325067+00:00
-- url     : https://prove2.me/theorems/41d328b9-d51f-49c3-8e31-a899b2f82bc8
-- title:
--   Haar block information bound with a finite state, I(S; W | V, B, BS) ≤ H(W | V)/m + Cd + log(1 + Cd + H(V)) + C(H(V) + log d)/d² (OpenAI posterior replicas, Proposition 7.5)
-- statement:
--   **The experiment.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$. A signal $S$ and a state $V \in \{0, \dots, V_0 - 1\}$ have a joint law $q$ whose first marginal is $\sigma_d$. Independently, $A$ is a $k \times d$ matrix with independent standard Gaussian rows, and a new state $W \in \{0, \dots, W_0 - 1\}$ is drawn from a Markov kernel $\kappa$ applied to $(V, A, AS)$ (`stateMessageLaw q κ` is the joint law of $((S, V), W)$). Independently of everything, $B$ is a Haar-distributed $\ell$-frame: $\ell$ standard Gaussian rows orthonormalized by Gram–Schmidt (`haarRows d ℓ`); the analyst sees $(V, B, BS)$ (`stateHaarSideLaw ℓ`). `cmi` is $I(S; W \mid V, B, BS)$, the relative entropy of the joint law from the product of the two conditional laws given $(V, B, BS)$. `finiteEntropy` is Shannon entropy in nats; $H(V)$ is the entropy of $V$ and `terminalConditionalEntropy` is $H(W \mid V) = H(V, W) - H(V)$.
--
--   **The statement.** There is a constant $C > 0$ such that for every $d \ge 64$, with $k = \lfloor d/16\rfloor$ and $\ell = \lfloor d/4\rfloor$, and for all $V_0, W_0 \ge 1$, every such $q$ and every Markov kernel $\kappa$,
--   $$I(S; W \mid V, B, BS) \;\le\; \frac{H(W \mid V)}{\lfloor d/16\rfloor + 1} + C d + \log\bigl(1 + C d + H(V)\bigr) + C\,\frac{H(V) + \log d}{d^2}.$$
--
--   This is the proposition `HaarReplicaBlock` of the published bundle `Def_PosteriorReplicas`, the fifth component of the goal `OAI.PosteriorReplicas.source_main`; it is the Lean form of the paper's Proposition 7.5.
--
--   Lean: `OAI.PosteriorReplicas.haarReplicaBlock`, OpenAI's theorem of that name (in `lean/OAI/Probability/PosteriorReplicas/Information/HaarStateBound.lean`).
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf, Proposition 7.5; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Information/HaarStateBound.lean (declaration OAI.PosteriorReplicas.haarReplicaBlock)

import Mathlib
import Definitions.Def_PosteriorReplicas

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

theorem haarReplicaBlock : HaarReplicaBlock := by
  sorry

end PosteriorReplicas
end

end OAI
end
