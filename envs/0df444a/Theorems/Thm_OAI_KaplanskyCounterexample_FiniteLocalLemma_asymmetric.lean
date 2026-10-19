-- Prove2me | Theorems.Thm_OAI_KaplanskyCounterexample_FiniteLocalLemma_asymmetric
-- name    : OAI.KaplanskyCounterexample.FiniteLocalLemma.asymmetric
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:37:22.225865+00:00
-- url     : https://prove2.me/theorems/8b33fc79-1efe-4d95-a683-1d70a8bd29f0
-- title:
--   The asymmetric Lovász Local Lemma (Erdős–Lovász), product form for finite families of events in a probability space
-- statement:
--   Let $(\Omega, \mu)$ be a probability space: `Ω : Type u_1` with `[MeasurableSpace Ω]`, and `μ : Measure Ω` with `[IsProbabilityMeasure μ]`. Write $P(S)$ for `μ.real S`, the measure of $S$ as a real number. Let `ι : Type u_2` be any index type (it need not be finite), let $E_i$ (`E : ι → Set Ω`) be events, let $x_i$ (`x : ι → ℝ`) be reals and let $\Gamma(i)$ (`Γ : ι → Finset ι`) be a finite set of indices for each $i$. For a finite set $s$ of indices (`s : Finset ι`) let
--   $$A_s \;=\; \bigcap_{j \in s} E_j^{\mathsf c} \qquad(\texttt{⋂ j ∈ s, (E j)ᶜ}),$$
--   the event that none of the $E_j$ with $j \in s$ occurs; $A_\emptyset = \Omega$. Assume:
--
--   1. (`hE`) every $E_i$ is measurable;
--   2. (`hx0`, `hx1`) $0 \le x_i$ and $x_i < 1$ for every $i$;
--   3. (`hind`) for every $i$ and every finite set $s$ with $i \notin s$ and $s$ disjoint from $\Gamma(i)$, $\;P(E_i \cap A_s) = P(E_i)\,P(A_s)$;
--   4. (`hprob`) for every $i$, $\;P(E_i) \le x_i \prod_{j \in \Gamma(i)} (1 - x_j)$.
--
--   Then for every finite set $s$ of indices,
--   $$0 < P(A_s) \qquad\text{and}\qquad P(E_i \cap A_s) \le x_i\, P(A_s) \ \text{ for every } i \notin s .$$
--
--   This is the asymmetric local lemma of Erdős and Lovász (1975), stated for every finite subfamily of events: the positivity of $P(A_s)$ says that with positive probability none of the events $E_j$, $j \in s$, occurs. Hypothesis 3 is the usual dependency-graph condition, that $E_i$ is independent of the events outside $\Gamma(i)$ jointly, written only for the intersections $A_s$ that the proof uses and as an equality of real probabilities. The set $\Gamma(i)$ may contain $i$ itself, which only weakens hypothesis 4. The second conclusion is the conditional bound $P(E_i \mid A_s) \le x_i$ written without division.
--
--   Lean: `OAI.KaplanskyCounterexample.FiniteLocalLemma.asymmetric`, OpenAI's lemma of that name in `lean/OAI/RingTheory/DirectFiniteness/SlabAvoidance.lean`. There the events $A_s$ are written `avoid E s`, a one-line definition equal to `⋂ i ∈ s, (E i)ᶜ`. This statement unfolds that definition and drops an unused `[DecidableEq ι]` hypothesis, so it needs only Mathlib. Otherwise the hypotheses and conclusion are OpenAI's.
-- source:
--   P. Erdős and L. Lovász, Problems and results on 3-chromatic hypergraphs and some related questions, in Infinite and Finite Sets (Colloq. Keszthely, 1973), Colloq. Math. Soc. János Bolyai 10, North-Holland, 1975, pp. 609–627 (the local lemma). Lean proof: OpenAI, A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 197; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/DirectFiniteness/SlabAvoidance.lean (declaration OAI.KaplanskyCounterexample.FiniteLocalLemma.asymmetric)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace KaplanskyCounterexample.FiniteLocalLemma

variable {Ω : Type u_1} {ι : Type u_2}

variable [DecidableEq ι]

variable [MeasurableSpace Ω]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : ι → Set Ω}

omit [DecidableEq ι] in
theorem asymmetric {x : ι → ℝ} (hE : ∀ i, MeasurableSet (E i))
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (Γ : ι → Finset ι)
    (hind : ∀ i (s : Finset ι), i ∉ s → Disjoint s (Γ i) →
      μ.real (E i ∩ ⋂ j ∈ s, (E j)ᶜ) = μ.real (E i) * μ.real (⋂ j ∈ s, (E j)ᶜ))
    (hprob : ∀ i, μ.real (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∀ s : Finset ι, 0 < μ.real (⋂ j ∈ s, (E j)ᶜ) ∧
      ∀ i ∉ s, μ.real (E i ∩ ⋂ j ∈ s, (E j)ᶜ) ≤ x i * μ.real (⋂ j ∈ s, (E j)ᶜ) := by
  sorry

end KaplanskyCounterexample.FiniteLocalLemma

end OAI
end
