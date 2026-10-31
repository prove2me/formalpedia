-- Prove2me | Theorems.Thm_FuchsThesis_Types_card_types_le
-- name    : FuchsThesis.Types.card_types_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:03.612668+00:00
-- url     : https://prove2.me/theorems/991b03ae-4505-4131-ab5d-abba172a237b
-- title:
--   The number of frequency vectors is at most $(n+1)^B$
-- statement:
--   Let $\mathcal F$ be the set of all empirical frequency vectors $(F_{\vec b}(1),\dots,F_{\vec b}(B))$ of strings $\vec b\in\{1,\dots,B\}^n$, where $F_{\vec b}(b)$ is the number of occurrences of $b$ in $\vec b$ divided by $n$. Then
--
--   $$
--   |\mathcal F|\le(n+1)^{B}.
--   $$
--
--   The number of frequency vectors thus grows only polynomially in $n$, while the number of strings grows exponentially. This is what makes the polynomial factor in the type-class bounds possible.
--
--   **Formalization Note** The cardinality is `Set.encard`, which is $\top$ on an infinite set, so the statement also asserts that $\mathcal F$ is finite.
--
--   Differences from the source:
--   - encoding: the source repeats the experiment n times and divides by n in (2.77) → Lean assumes `1 ≤ n`; reason: excludes the undefined case n = 0.
--   - encoding: |F| → `Set.encard` of `possibleTypes B n`; reason: the same number, with no junk value on infinite sets.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3.2, p.25

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Types

set_option autoImplicit false

open ModernOnlineLearning.Portfolio

namespace FuchsThesis.Types

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.3.2, text before (2.79), p.25 (PDF 34): the set `F` of all possible
frequency vectors (2.78) of strings of length `n` over `B` outcomes has cardinality at most
`(n + 1)^B`.

**Formalization Note.** `F` is `possibleTypes B n`, a `Set (Fin B → ℝ)`. The bound uses `Set.encard`,
which takes the value `⊤` on an infinite set, so it also asserts that `F` is finite; `n ≥ 1` is the
source's setting, in which (2.77) is defined. -/
theorem card_types_le (B n : ℕ) (hn : 1 ≤ n) :
    (possibleTypes B n).encard ≤ (((n + 1) ^ B : ℕ) : ℕ∞) := by sorry

end FuchsThesis.Types
