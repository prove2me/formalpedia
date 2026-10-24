-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_incidenceReplicaBlock
-- name    : OAI.PosteriorReplicas.incidenceReplicaBlock
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:32:05.868542+00:00
-- url     : https://prove2.me/theorems/6265bf9d-05ca-4eaf-b84a-ab639cb29745
-- title:
--   Block bound in one block, I(S; W | B, BS) ≤ log N/⌊d/16⌋ + Cd + C log(1 + log F) (OpenAI posterior replicas, cf. Proposition 9.1)
-- statement:
--   **The block experiment.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$. A signal $S$ has a law $p$ on $\mathbb R^d$. Independently, $A$ is a $k \times d$ matrix with independent standard Gaussian rows (`gaussianRows d k`), and a message $W \in \{0, \dots, N-1\}$ is drawn from a Markov kernel $\kappa$ applied to $(A, AS)$ (`signalMessageLaw p κ` is the joint law of $(S, W)$). Independently, $B$ is an $\ell \times d$ standard Gaussian matrix and the analyst sees $(B, BS)$ (`sideLaw ℓ`). `conditionalInformation` is $I(S; W \mid B, BS)$, the relative entropy of the joint law from the product of the two conditional laws given $(B, BS)$.
--
--   **The statement.** There are a constant $C > 0$ and a $d_0$ such that for every $d \ge d_0$ the following holds, with $k = \lfloor d/16\rfloor$ message rows and $\ell = \lfloor d/4\rfloor$ side rows. Let $F \ge 1$, let $f : \mathbb R^d \to \mathbb R$ be measurable with $0 \le f \le F$, and let $p = f\,\sigma_d$ be a probability measure. Then for every $N \ge 1$ and every Markov kernel $\kappa$,
--   $$I(S; W \mid B, BS) \;\le\; \frac{\log N}{\lfloor d/16\rfloor} + C d + C \log(1 + \log F).$$
--
--   This is the proposition `IncidenceReplicaBlock` of the published bundle `Def_PosteriorReplicas`, the seventh component of the goal `OAI.PosteriorReplicas.source_main`. It has the shape of the paper's Proposition 9.1 (information in one block), with these row counts.
--
--   Lean: `OAI.PosteriorReplicas.incidenceReplicaBlock`, OpenAI's theorem of that name (in `lean/OAI/Probability/PosteriorReplicas/Information/HeadlineInformation.lean`).
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf, cf. Proposition 9.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Information/HeadlineInformation.lean (declaration OAI.PosteriorReplicas.incidenceReplicaBlock)

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

theorem incidenceReplicaBlock : IncidenceReplicaBlock := by
  sorry

end PosteriorReplicas
end

end OAI
end
