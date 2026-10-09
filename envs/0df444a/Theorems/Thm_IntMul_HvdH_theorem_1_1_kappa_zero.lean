-- Prove2me | Theorems.Thm_IntMul_HvdH_theorem_1_1_kappa_zero
-- name    : IntMul.HvdH.theorem_1_1_kappa_zero
-- status  : Open
-- author  : @avi
-- created : 2026-10-08T17:36:22.246265+00:00
-- url     : https://prove2.me/theorems/18b79a4a-90d3-4c7b-9181-4cb193d4a7d4
-- title:
--   Theorem 1.1 in the $\kappa$-framework — $\mathrm{KappaBound}(0)$: multiplication in time $O(n\lg n)$
-- statement:
--   **Theorem 1.1 of Harvey–van der Hoeven, in the $\kappa$-framework.** $\mathrm{KappaBound}(0)$ holds: there is one deterministic multitape Turing machine that, for every $n\ge1$ and all $x,y\in\{0,1\}^n$, halts on input $x\#y$ with output $\operatorname{bin}_{2n}(\operatorname{val}(x)\operatorname{val}(y))$, and whose worst-case running time $T(n)$ satisfies
--   $$T(n)=O\big(n(\lg n)^{1-0}\big)=O(n\lg n),\qquad\lg n=\max(\lceil\log_2n\rceil,1).$$
--
--   This is the paper's main theorem, written in the same form as the claimed improvements $\mathrm{KappaBound}(\kappa)$ with $\kappa>0$. It is the baseline of that family of bounds.
--
--   **Formalization Note** $\mathrm{KappaBound}(\kappa)$ is defined in `IntMul_MultitapeModel`, which uses the $k$-tape Turing machine conventions of Montanaro's lecture notes (start symbol, $\mathrm{HALT}$ state, read-only input tape, separate output tape). It asserts a single machine that, for every $n\ge1$ and all $x,y\in\{0,1\}^n$, halts on input $x\#y$ with output $\operatorname{bin}_{2n}(\operatorname{val}(x)\operatorname{val}(y))$, and whose worst-case running time is at most $c\,n(\lg n)^{1-\kappa}$ for all $n\ge n_0$, for some $c>0$ and $n_0$. Here $\lg n=\max(\lceil\log_2n\rceil,1)$.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021) 563-617, https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §1, Theorem 1.1, p. 1, restated with lg n = max(ceil(log2 n),1) as in OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf, §1

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.HvdH

theorem theorem_1_1_kappa_zero : KappaBound 0 := by sorry

end IntMul.HvdH
