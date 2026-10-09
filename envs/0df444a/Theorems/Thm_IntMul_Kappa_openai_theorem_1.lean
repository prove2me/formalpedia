-- Prove2me | Theorems.Thm_IntMul_Kappa_openai_theorem_1
-- name    : IntMul.Kappa.openai_theorem_1
-- status  : Open
-- author  : @avi
-- created : 2026-10-08T17:47:40.586983+00:00
-- url     : https://prove2.me/theorems/60e37d6f-88a9-4bc4-b925-6e7ec3460fc3
-- title:
--   OpenAI Theorem 1 — multiplication in time $O(n(\lg n)^{1-\kappa})$, $\kappa=2^{-182}$
-- statement:
--   **Theorem 1 of the OpenAI preprint *Integer multiplication below $n\log n$*.** There is one deterministic Turing machine $A$, with a fixed finite alphabet and a fixed finite number of one-dimensional tapes, that computes the exact product for every $n\ge1$ and every pair of $n$-bit inputs: on input $x\#y$ with $x,y\in\{0,1\}^n$ it outputs $\operatorname{bin}_{2n}(\operatorname{val}(x)\operatorname{val}(y))$. Its worst-case running time satisfies
--   $$T_A(n)=O\big(n(\lg n)^{1-\kappa}\big),\qquad\kappa=2^{-182},$$
--   where $\lg n=\max(\lceil\log_2n\rceil,1)$.
--
--   If true, this shows that $n\log n$ is not the optimal order of growth for multiplication on multitape Turing machines. The preprint has not been refereed.
--
--   **Formalization Note** $\mathrm{KappaBound}(\kappa)$ is defined in `IntMul_MultitapeModel`, which uses the $k$-tape Turing machine conventions of Montanaro's lecture notes (start symbol, $\mathrm{HALT}$ state, read-only input tape, separate output tape). It asserts a single machine that, for every $n\ge1$ and all $x,y\in\{0,1\}^n$, halts on input $x\#y$ with output $\operatorname{bin}_{2n}(\operatorname{val}(x)\operatorname{val}(y))$, and whose worst-case running time is at most $c\,n(\lg n)^{1-\kappa}$ for all $n\ge n_0$, for some $c>0$ and $n_0$. Here $\lg n=\max(\lceil\log_2n\rceil,1)$.
-- source:
--   OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf, §1, Theorem 1 (thm:main); manuscript commit adc7f1241b42e322a6451854ab7e4b4c146bf78a

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.Kappa

theorem openai_theorem_1 : KappaBound (1 / 2 ^ 182) := by sorry

end IntMul.Kappa
