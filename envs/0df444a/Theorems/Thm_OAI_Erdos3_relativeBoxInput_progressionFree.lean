-- Prove2me | Theorems.Thm_OAI_Erdos3_relativeBoxInput_progressionFree
-- name    : OAI.Erdos3.relativeBoxInput_progressionFree
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T20:26:14.188312+00:00
-- url     : https://prove2.me/theorems/6d33b711-52fc-4ed3-b185-114e39fa2284
-- title:
--   Restricting an input to the box keeps its in-box support free of k-term progressions
-- statement:
--   Let $X$ be a finite type, $N : X \to \mathbb{N}$, $f : \mathbb{Z}^X \to \mathbb{R}$ and $k \in \mathbb{N}$. Write `integerBox N` for the finite box $\prod_{i \in X} \{0, 1, \dots, N_i - 1\} \subseteq \mathbb{Z}^X$, and `relativeBoxInput N f` for the function equal to $f$ on `integerBox N` and to $0$ outside it. Here `IntegerVectorAPFree A k` (for $A \subseteq \mathbb{Z}^X$) means: for all $a, d \in \mathbb{Z}^X$ with $d \ne 0$ there is $i \in \{0, \dots, k-1\}$ with $a + i d \notin A$. Assume `IntegerVectorAPFree` $\{x \mid x \in \texttt{integerBox}\ N \wedge f(x) \ne 0\}$ $k$. Then `IntegerVectorAPFree` $\{x \mid x \in \texttt{integerBox}\ N \wedge \texttt{relativeBoxInput}\ N\ f\ x \ne 0\}$ $k$.
--
--   Lean: `OAI.Erdos3.relativeBoxInput_progressionFree` in `lean/OAI/Combinatorics/Progressions/Geometry/RelativePatchBoxRestriction.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B099` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/RelativePatchBoxRestriction.lean#L38

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B099

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativeBoxInput_progressionFree {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree {x | x ∈ integerBox N ∧ relativeBoxInput N f x ≠ 0} k := by
  sorry

end Erdos3
end
end OAI
