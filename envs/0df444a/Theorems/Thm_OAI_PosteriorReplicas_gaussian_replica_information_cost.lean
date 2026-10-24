-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_gaussian_replica_information_cost
-- name    : OAI.PosteriorReplicas.gaussian_replica_information_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:34:12.404379+00:00
-- url     : https://prove2.me/theorems/ca0e0de2-98d7-4318-8331-a80b26127a91
-- title:
--   Replica information bound with explicit cost, I(S; W | B, BS) ≤ (H(W) + comparisonCost)/(m + 1) (OpenAI posterior replicas)
-- statement:
--   **The block experiment.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$ and $\nu = f\sigma_d$. A signal $S \sim \nu$; independently, $A$ is a $k \times d$ matrix with independent standard Gaussian rows, and a message $W \in \{0, \dots, N-1\}$ is drawn from a Markov kernel $\kappa$ applied to $(A, AS)$ (`signalMessageLaw ν κ` is the joint law of $(S, W)$). Independently, $B$ is an $\ell \times d$ standard Gaussian matrix and the analyst sees $(B, BS)$ (`sideLaw ℓ`). `conditionalInformation` is $I(S; W \mid B, BS)$, the relative entropy of the joint law from the product of the two conditional laws given $(B, BS)$, and `messageEntropy` is $H(W)$ in nats.
--
--   **The cost.** Let $Z$ (`wishartMoment ℓ m k`) be $\mathbb E\bigl[\mathrm{vol}(G)^{-k}\bigr]$ for $m$ independent standard Gaussian vectors $G$ in $\mathbb R^\ell$, where $\mathrm{vol}$ is the square root of the Gram determinant, and let $\beta_{k,J} = \mathrm{vol}\{v \in \mathbb R^k : |v| \le 1\}\,(2 + J\,2^k)$ (`binMeanBound`). The comparison cost (`comparisonCost d ℓ k m J`) is
--   $$\log Z + k\,\frac{m}{2}\log(\ell + 1) + m\,\frac{k}{2}\log(d + 1) + m \log \beta_{k,J}.$$
--
--   **The statement.** Let $N \ge 1$ and $k, m \ge 1$ with $4k + m + 2 \le d$ and $k + m \le \ell$. Let $f \ge 0$ be measurable with $f \le L$ for a finite $L$, let $\nu = f\sigma_d$ be a probability measure, let $\kappa$ be a Markov kernel from $k$ rows and their labels to $\{0, \dots, N-1\}$, and let $J$ satisfy
--   $$L \cdot 72^d \cdot 2^{-J} \cdot (1 + 2^{k+1}) \le 1.$$
--   Then
--   $$I(S; W \mid B, BS) \;\le\; \frac{H(W) + \texttt{comparisonCost}\ d\ \ell\ k\ m\ J}{m + 1}$$
--   (the right side is passed through `ENNReal.ofReal`, so it is read as $0$ if negative).
--
--   Lean: `OAI.PosteriorReplicas.gaussian_replica_information_cost`, OpenAI's lemma of that name (in `lean/OAI/Probability/PosteriorReplicas/Information/ReplicaInformationBound.lean`). `comparisonCost`, `binMeanBound` and `wishartMoment` come from the definitions bundle `OAIQWPR000` of this split.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Information/ReplicaInformationBound.lean (declaration OAI.PosteriorReplicas.gaussian_replica_information_cost)

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000

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

lemma gaussian_replica_information_cost {d ℓ k m N : ℕ} [NeZero N]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    conditionalInformation (sideLaw ℓ (signalMessageLaw ((sphereLaw d).withDensity f) κ)) ≤
      ENNReal.ofReal ((messageEntropy (signalMessageLaw ((sphereLaw d).withDensity f) κ)+
        comparisonCost d ℓ k m J)/((m+1:ℕ):ℝ)) := by
  sorry

end PosteriorReplicas
end

end OAI
end
