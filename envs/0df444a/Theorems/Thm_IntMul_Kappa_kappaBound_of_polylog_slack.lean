-- Prove2me | Theorems.Thm_IntMul_Kappa_kappaBound_of_polylog_slack
-- name    : IntMul.Kappa.kappaBound_of_polylog_slack
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:27:25.769349+00:00
-- url     : https://prove2.me/theorems/ad751c7f-0844-41c4-af6d-8cdd3bca95a2
-- title:
--   Exponent slack absorbs a polylogarithmic factor in the multiplication time
-- statement:
--   **A polylogarithmic factor is absorbed by any slack in the exponent.** Let $M$ be a deterministic multitape Turing machine that multiplies correctly at every input length $n\ge1$. Suppose that for real numbers $\kappa<g$, a constant $C$, a natural number $A$ and all $n\ge n_0$, its worst-case running time on $n$-bit inputs is at most
--   $$C\,n\,(\lg n)^{1-g}\,\big(\ln \lg n+1\big)^{A},\qquad \lg n=\max(\lceil\log_2 n\rceil,1).$$
--   Then $\mathrm{KappaBound}(\kappa)$ holds: multiplication runs in time $O\big(n(\lg n)^{1-\kappa}\big)$.
--
--   This is the last step of the cost accounting in the OpenAI manuscript and in the community rounds: each cost row is a power of $\lg n$ at most $1-g$ with every margin $g$ above $\kappa$, and any fixed power of $\log\lg n$ is then absorbed into the slack $g-\kappa$.
--
--   **Formalization Note** $\mathrm{KappaBound}$, $\mathrm{MultipliesAt}$ and $\lg$ are from `IntMul_MultitapeModel`. No sign condition on $C$ is needed.
-- source:
--   OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 'The complete time bound' (each displayed power is at most 1-2κ; any fixed power of log p is at most p^κ eventually)

import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.Kappa

theorem kappaBound_of_polylog_slack (κ g C : ℝ) (A : ℕ) (hg : κ < g) (M : MultitapeTM)
    (hcorr : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, MultipliesAt M n T) (n₀ : ℕ)
    (hT : ∀ n : ℕ, n₀ ≤ n →
      MultipliesAt M n (C * n * (lg n : ℝ) ^ (1 - g) * (Real.log (lg n) + 1) ^ A)) :
    KappaBound κ := by sorry

end IntMul.Kappa
