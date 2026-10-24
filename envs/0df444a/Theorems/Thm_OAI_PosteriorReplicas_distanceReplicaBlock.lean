-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_distanceReplicaBlock
-- name    : OAI.PosteriorReplicas.distanceReplicaBlock
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:30:54.53806+00:00
-- url     : https://prove2.me/theorems/39fa260a-3d10-4312-acf5-d06435f72d15
-- title:
--   Block bound with density at most e^b, I(S; W | B, BS) ≤ H(W)/⌊d/8⌋ + C(d + b/d) (OpenAI posterior replicas, cf. Theorem 5.1)
-- statement:
--   **The block experiment.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$. A signal $S$ has a law $p$ on $\mathbb R^d$. Independently, $A$ is a $k \times d$ matrix with independent standard Gaussian rows (`gaussianRows d k`), and a message $W \in \{0, \dots, N-1\}$ is drawn from a Markov kernel $\kappa$ applied to $(A, AS)$ (`signalMessageLaw p κ` is the joint law of $(S, W)$). Independently, $B$ is an $\ell \times d$ standard Gaussian matrix and the analyst sees $(B, BS)$ (`sideLaw ℓ`). `conditionalInformation` is $I(S; W \mid B, BS)$, the relative entropy of the joint law from the product of the two conditional laws given $(B, BS)$, and `messageEntropy` is $H(W)$ in nats.
--
--   **The statement.** There are a constant $C > 0$ and a $d_0$ such that for every $d \ge d_0$ the following holds, with $k = \lfloor d/16\rfloor$ message rows and $\ell = \lfloor d/2\rfloor$ side rows. Let $b \ge 0$, let $f : \mathbb R^d \to \mathbb R$ be measurable with $0 \le f \le e^b$, and let $p = f\,\sigma_d$ be a probability measure. Then for every $N \ge 1$ and every Markov kernel $\kappa$,
--   $$I(S; W \mid B, BS) \;\le\; \frac{H(W)}{\lfloor d/8\rfloor} + C\Bigl(d + \frac{b}{d}\Bigr).$$
--
--   This is the proposition `DistanceReplicaBlock` of the published bundle `Def_PosteriorReplicas`, the fourth component of the goal `OAI.PosteriorReplicas.source_main`. It has the shape of the paper's Theorem 5.1 (information from shared exact data), with these row counts.
--
--   Lean: `OAI.PosteriorReplicas.distanceReplicaBlock`, OpenAI's theorem of that name (in `lean/OAI/Probability/PosteriorReplicas/Information/HeadlineInformation.lean`).
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf, cf. Theorem 5.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Information/HeadlineInformation.lean (declaration OAI.PosteriorReplicas.distanceReplicaBlock)

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

theorem distanceReplicaBlock : DistanceReplicaBlock := by
  sorry

end PosteriorReplicas
end

end OAI
end
