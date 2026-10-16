-- Prove2me | Theorems.Thm_OAI_Erdos3_manuscript_main_theorems
-- name    : OAI.Erdos3.manuscript_main_theorems
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:56:55.909499+00:00
-- url     : https://prove2.me/theorems/c00ba02e-a967-4dac-a170-1defa7a289c0
-- title:
--   The quantitative density theorem and the reciprocal progression theorem both hold
-- statement:
--   Both `QuantitativeDensityTheorem` and `ReciprocalProgressionTheorem` hold. The first says: for every natural number $k \ge 3$ there are reals $C, c, \eta > 0$ such that for every natural number $N \ge 3$,
--   $$\mathrm{extremalNumber}(k, N) \le C\, N \exp\bigl(-c\,(\log\log N)^{1+\eta}\bigr),$$
--   where `extremalNumber k N` is the largest cardinality of a subset $S \subseteq \{1, \dots, N\}$ that contains no $k$-term arithmetic progression (no $a, d \in \mathbb N$ with $d > 0$ and $a + i d \in S$ for all $i < k$). The second says: for every set $A \subseteq \mathbb N$ such that the sequence $n \mapsto 1/n$ for $n \in A$ (and $0$ for $n \notin A$) is not summable, and every natural number $k$, there are $a, d \in \mathbb N$ with $d > 0$ and $a + i d \in A$ for all $i < k$.
--
--   Lean: `OAI.Erdos3.manuscript_main_theorems` in `lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1324` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean#L26

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1324

namespace OAI

section

namespace Erdos3

theorem manuscript_main_theorems :
    QuantitativeDensityTheorem ∧ ReciprocalProgressionTheorem := by
  sorry

end Erdos3
end
end OAI
