-- Prove2me | Theorems.Thm_OAI_CurrentProjection_critical_refined_comparison
-- name    : OAI.CurrentProjection.critical_refined_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:58:36.588848+00:00
-- url     : https://prove2.me/theorems/681fa156-3b94-49c8-8c18-e1108b4e41d8
-- title:
--   Refined critical-radius comparison of fresh and aligned exposed information, with explicit error terms (OpenAI Gaussian replacement, proof of Theorem 4.1)
-- statement:
--   **Notation** (from the published bundle `Def_GaussianReplacement` and the definitions bundle `OAIQWCP000` of this split). $\sigma_d$ (`uniformSphere d`) is the uniform probability on the unit sphere of $\mathbb R^d$ and $\gamma_{k,d}$ (`gaussianRows k d`) the law of $k$ independent standard Gaussian rows. For a law on ((signal $S$, message $W$), rows $G$), `exposedInformation` is the conditional mutual information $I(S; W \mid G, GS)$, written as the relative entropy from the product of the two conditional laws given $(G, GS)$. `rowInformation R γ` is the relative entropy of $R$ from (its (signal, message) marginal) $\otimes\,\gamma$. `shannonEntropy` is $\int -\log \pi\{w\}\,d\pi(w)$. `alignedExperiment (r := r) R` appends $r$ independent standard Gaussian rows to the rows of $R$.
--
--   **The critical refinement.** For a law $P$ of (signal, message) and $\ell \in \mathbb N$, let $F_w$ be the conditional law of the signal given $W = w$ (`messagePosterior`). With radii $R_j = 2 \cdot 2^{-j}$ (`criticalRadius`), the ball ratio at $s$ is $F_w(\{x : |x - s| \le R_j\})/R_j^{\ell}$ (`ballRatio`). `criticalRefinement P ℓ` labels $(s, w)$ by the least index $j$ maximizing the ball ratio (`criticalIndex`, $0$ if there is no maximum) and by $\lceil \log \rceil$ of that maximal ratio (`criticalLevel`). `criticalSignal P ℓ` is the law of (signal, (message, label)).
--
--   **The statement.** Let $W$ be countable, nonempty, with measurable singletons, and let $d, m, r, q$ satisfy `AdmissibleDimensions` ($m, r, q \ge 1$, $m + r < d - 1$, $r \ge q$). Let $P$ be a probability measure on (signal, message) with signal marginal $\sigma_d$ and finite message entropy. Write $P' = $ `criticalSignal P (m+r)`. Let $R$ be a probability measure on ((signal, refined message), $m$ rows) whose (signal, refined message) marginal is $P'$ and whose (signal, rows) marginal is $\sigma_d \otimes \gamma_{m,d}$. Then both exposed informations below are finite, and
--   $$I_{\mathrm{exp}}\bigl(P' \otimes \gamma_{m+r,d}\bigr) \;\le\; I_{\mathrm{exp}}\bigl(\mathrm{aligned}_r(R)\bigr) + \frac{\mathrm{rowInformation}(R, \gamma_{m,d})}{q} + H\bigl(\text{label}\bigr) + 1 + 18d + 5(m + r) + \log\bigl(1 + H(\text{refined message})\bigr),$$
--   where $H(\text{label})$ is the entropy of the law of `criticalRefinement P (m+r)` under $P$ and $H(\text{refined message})$ that of the message marginal of $P'$ (all as real numbers).
--
--   The statement also takes as instance arguments that the sphere is nonempty and that $\sigma_d$ is a probability measure. The proof of the goal `OAI.CurrentProjection.criticalComparisonMain` (the paper's Theorem 4.1) applies this lemma and then bounds the error terms by $O(d)$.
--
--   Lean: `OAI.CurrentProjection.critical_refined_comparison`, OpenAI's lemma of that name (in `lean/OAI/Probability/GaussianReplacement/Comparison.lean`). `criticalSignal`, `criticalRefinement`, `criticalIndex`, `criticalLevel`, `ballRatio` and `criticalRadius` come from the definitions bundle `OAIQWCP000`.
-- source:
--   OpenAI, Replacing Gaussian observations in memory-constrained inference, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf, proof of Theorem 4.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianReplacement/Comparison.lean (declaration OAI.CurrentProjection.critical_refined_comparison)

import Mathlib
import Definitions.Def_GaussianReplacement
import Definitions.Def_OAIQWCP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

lemma critical_refined_comparison {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty W] [Nonempty (Sphere d)]
    [IsProbabilityMeasure (uniformSphere d)] (hdim : AdmissibleDimensions d m r q)
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hH : shannonEntropy P.snd ≠ ∞)
    (R : Measure ((Sphere d×(W×(ℕ×ℤ)))×Rows m d)) [IsProbabilityMeasure R]
    (hRF : R.fst = criticalSignal P (m+r))
    (hInd : (R.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d)) :
    exposedInformation ((criticalSignal P (m+r)).prod (gaussianRows (m+r) d)) ≠ ∞ ∧
    exposedInformation (alignedExperiment (r:=r) R) ≠ ∞ ∧
    (exposedInformation ((criticalSignal P (m+r)).prod (gaussianRows (m+r) d))).toReal ≤
      (exposedInformation (alignedExperiment (r:=r) R)).toReal +
      (rowInformation R (gaussianRows m d)).toReal/q +
      (shannonEntropy (P.map (criticalRefinement P (m+r)))).toReal +
      (1+18*(d:ℝ)+5*(m+r)) + Real.log (1+(shannonEntropy (criticalSignal P (m+r)).snd).toReal) := by
  sorry

end CurrentProjection

end

end OAI
end
