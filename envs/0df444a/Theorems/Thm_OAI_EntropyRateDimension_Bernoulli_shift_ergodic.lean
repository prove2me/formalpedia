-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Bernoulli_shift_ergodic
-- name    : OAI.EntropyRateDimension.Bernoulli.shift_ergodic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T18:32:48.165046+00:00
-- url     : https://prove2.me/theorems/1acbb306-0175-4cdd-96cd-4a544610f9d4
-- title:
--   Bernoulli shifts are ergodic: the left shift on sequences is ergodic for every infinite product of a probability measure
-- statement:
--   Let $\alpha$ be a type with a measurable space structure, and let $p$ be a probability measure on $\alpha$ (`IsProbabilityMeasure p`). Let $p^{\otimes \mathbb N}$ be the infinite product measure on the sequence space $\alpha^{\mathbb N} = (\mathbb N \to \alpha)$, with its product measurable structure (Mathlib's `Measure.infinitePi (fun _ : ℕ => p)`), and let $\sigma : \alpha^{\mathbb N} \to \alpha^{\mathbb N}$ be the left shift, $\sigma(\omega)(n) = \omega(n+1)$ (in Lean `fun ω : ℕ → α => fun n => ω (n + 1)`). Then $\sigma$ is ergodic for $p^{\otimes \mathbb N}$:
--   $$\texttt{Ergodic}\ \sigma\ \bigl(p^{\otimes \mathbb N}\bigr).$$
--   That is, in Mathlib's sense of `Ergodic`: $\sigma$ is measurable and preserves $p^{\otimes \mathbb N}$ (`MeasurePreserving`), and every measurable set $s \subseteq \alpha^{\mathbb N}$ with $\sigma^{-1}(s) = s$ is almost everywhere constant, `EventuallyConst s (ae (Measure.infinitePi fun _ => p))`, which means that $s$ has measure $0$ or its complement has measure $0$.
--
--   This is the classical fact that Bernoulli shifts are ergodic, here for an arbitrary probability measure $p$ on an arbitrary measurable space.
--
--   Lean: `OAI.EntropyRateDimension.Bernoulli.shift_ergodic`, OpenAI's theorem of that name (in `lean/OAI/MeasureTheory/SelfSimilar/Bernoulli.lean`), with the universe `uα` of $\alpha$ arbitrary. OpenAI states it for their definition `Bernoulli.shift`, which is $\omega \mapsto (n \mapsto \omega(n+1))$ by definition; this statement writes that map out, so it uses only Mathlib's definitions (`Ergodic`, `Measure.infinitePi`, `IsProbabilityMeasure`) and imports no definitions bundle.
-- source:
--   Classical; the proof is through Kolmogorov's zero–one law (A. N. Kolmogorov, Grundbegriffe der Wahrscheinlichkeitsrechnung, Springer, 1933); proof and Lean code: OpenAI, The entropy-rate dimension formula for self-similar measures on the line, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 148; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/SelfSimilar/Bernoulli.lean (declaration OAI.EntropyRateDimension.Bernoulli.shift_ergodic)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace EntropyRateDimension
namespace Bernoulli

variable {α : Type uα} [MeasurableSpace α]

theorem shift_ergodic (p : Measure α) [IsProbabilityMeasure p] :
    Ergodic (fun ω : ℕ → α => fun n => ω (n + 1)) (Measure.infinitePi (fun _ : ℕ => p)) := by
  sorry

end Bernoulli
end EntropyRateDimension
end

end OAI
end
