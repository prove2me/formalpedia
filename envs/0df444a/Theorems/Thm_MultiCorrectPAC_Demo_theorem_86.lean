-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_theorem_86
-- name    : MultiCorrectPAC.Demo.theorem_86
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:46:46.817956+00:00
-- url     : https://prove2.me/theorems/4400d57f-8927-4e44-80b8-9203c68fafa9
-- title:
--   Theorem 86 (Theorem G(a)) — without a uniform bound on correct-label sets, no finite-witness parameter characterizes learnability and no parameter bounds the sample complexity
-- statement:
--   Fix either full-set or one-correct-label feedback. Let $\mathcal X$ and $\mathcal Y$ be countably infinite, and consider countable classes $\mathcal H$ of total hypotheses with $1\le|h(x)|<\infty$ for all $h\in\mathcal H$, $x\in\mathcal X$.
--
--   (i) There is no parameter $D$ with the finite-witness property such that $D(\mathcal H)<\infty$ if and only if $\mathcal H$ is realizably PAC learnable.
--
--   (ii) There is no pair $(D,\Psi)$ of a parameter $D$ that is finite on every realizably learnable class and a function $\Psi:\mathbb N_0\times(0,1)^2\to[0,\infty)$ such that
--   $$m_{\mathcal H}(\varepsilon,\delta)\le\Psi\big(D(\mathcal H),\varepsilon,\delta\big)\tag{90}$$
--   for every realizably learnable class $\mathcal H$ and all $\varepsilon,\delta\in(0,1)$.
--
--   The uniform bound $\ell$ on the number of correct labels is what makes the dimension characterizations of Theorems 41, 45 and 55 possible.
--
--   Differences from the source:
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - encoding: total hypotheses from X to the nonempty finite subsets of Y; countable classes → h : X → Finset Y; Considered H (countable, nonempty, all values nonempty); learnability through embedClass (x ↦ some (h x)); reason: Lean convention; the errors and Definition 1 are unchanged
--   - encoding: "fix either full-set or one-correct-label feedback" → ∀ fb : Feedback, with LearnableFb fb and sampleCx fb; reason: both models covered
--   - encoding: Ψ : ℕ₀ × (0,1)² → [0, ∞); (90) with m_H ∈ ℕ₀ ∪ {∞} → Ψ : ℕ → ℝ → ℝ → ℝ, nonnegative on (0,1)²; (90) as ∃ m : ℕ, sampleCx fb H ε δ = m ∧ (m : ℝ) ≤ Ψ d ε δ where D H = d; reason: values of Ψ outside (0,1)² are never used; an infinite sample complexity violates (90), as in the paper
--   - encoding: a parameter assigns a value to every nonempty class under consideration → D : Set (X → Finset Y) → ℕ∞; FiniteWitness and the iff are required on considered classes only; reason: values on other sets are irrelevant
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), pp. 99–100 (PDF 101–102), Theorem 86, (90)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning
import Definitions.Def_MultiCorrectPAC_Demo_ScaleFree

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem theorem_86 (fb : Feedback) {X Y : Type*} [Countable X] [Infinite X] [Countable Y]
    [Infinite Y] :
    (¬ ∃ D : Set (X → Finset Y) → ℕ∞, FiniteWitness D ∧
      ∀ H, Considered H → (D H < ⊤ ↔ LearnableFb fb H)) ∧
    (¬ ∃ (D : Set (X → Finset Y) → ℕ∞) (Ψ : ℕ → ℝ → ℝ → ℝ),
      (∀ H, Considered H → LearnableFb fb H → D H < ⊤) ∧
      (∀ (n : ℕ) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 → 0 ≤ Ψ n ε δ) ∧
      ∀ H, Considered H → LearnableFb fb H →
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ d : ℕ, D H = d →
          ∃ m : ℕ, sampleCx fb H ε δ = m ∧ (m : ℝ) ≤ Ψ d ε δ) := by sorry

end MultiCorrectPAC.Demo
