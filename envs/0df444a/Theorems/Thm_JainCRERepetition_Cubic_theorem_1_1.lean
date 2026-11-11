-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_theorem_1_1
-- name    : JainCRERepetition.Cubic.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:25.003374+00:00
-- url     : https://prove2.me/theorems/14cd522e-b6d2-49ad-83f9-957ade4ccd80
-- title:
--   Theorem 1.1 — cubic repetition using Song's sampler
-- statement:
--   There is one universal constant $c>0$ such that every finite two-player game $G$ with nonempty answer alphabets $A,B$, arbitrary normalized question law $\mu$ and gap $\varepsilon=1-\omega^*(G)>0$ satisfies, for every integer $n\ge1$,
--
--   $$\omega^*(G^{\otimes n})\le\exp\!\left[-\frac{c\varepsilon^3 n}{L}\right],\qquad L=\max\{1,\log_2(|A||B|)\}.$$
--
--   The entangled values are suprema over all finite local dimensions, arbitrary shared density matrices and local POVMs. Question pairs are independent across coordinates, while the two questions in each pair may be arbitrarily correlated and have sparse support. Joint local measurements across all questions are allowed; neither supremum is assumed attained.
--
--   The proof supplies $c=1/(128C_{\rm ext}^4)$ in Eq. (52), where $C_{\rm ext}=2^{1/4}\sqrt{100C_{\rm sm}}+\sqrt{\ln2}$ and $C_{\rm sm}\ge1$ is the universal constant of Fact 2.23. This recovers the exact cubic exponent for every $n\ge1$, including singleton answer alphabets through the definition of $L$.
--
--   Differences from the source:
--   - encoding: finite games under the usual nonempty-answer convention → the published QuantumParallelRepetition.Game and explicit Nonempty answer instances; reason: all finite alphabets and unrestricted finite-dimensional strategies are retained; normalized question mass already excludes empty question alphabets
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 2, Theorem 1.1; pp. 33–34, proof, Eq. (52); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_quantum

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem theorem_1_1 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        [Nonempty A] [Nonempty B] (G : QuantumParallelRepetition.Game X Y A B),
        0 < 1 - QuantumParallelRepetition.entangledValue G →
        ∀ n : ℕ, 1 ≤ n →
          QuantumParallelRepetition.repeatedEntangledValue G n ≤
            Real.exp (-c * (1 - QuantumParallelRepetition.entangledValue G)^3 * n /
              max 1 (Real.logb 2 ((Fintype.card A : ℝ) * Fintype.card B))) := by sorry
end JainCRERepetition.Cubic
