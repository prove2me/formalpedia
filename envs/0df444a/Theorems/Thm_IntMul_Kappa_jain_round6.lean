-- Prove2me | Theorems.Thm_IntMul_Kappa_jain_round6
-- name    : IntMul.Kappa.jain_round6
-- status  : Open
-- author  : @avi
-- created : 2026-10-08T17:49:13.31282+00:00
-- url     : https://prove2.me/theorems/9963d73f-fab7-44ad-b490-192b4d9f47b1
-- title:
--   Jain round six — multiplication in time $O(n(\lg n)^{1-\kappa})$, $\kappa=3666565558019/10^{17}>2^{-15}$
-- statement:
--   **Jain's round-six witness.** In the fixed finite-alphabet Turing-machine model with a fixed number of one-dimensional tapes, two $n$-bit integers can be multiplied exactly in time
--   $$T(n)=O\big(n(\lg n)^{1-\kappa}\big),\qquad\kappa=\frac{3666565558019}{10^{17}}\approx3.66657\times10^{-5}>2^{-15}.$$
--
--   This is the strongest exponent saving claimed so far in the line of work started by the OpenAI preprint. It combines copied retained centres, retained point totals and a two-stage complex interchange with the networks and parameter assembly of the earlier drafts. The project states that the claim is conditional on the OpenAI manuscript and on Colkitt's framework, and has not had independent review. Its moment certificates and parameter assembly are checked in the Lean kernel, with the analytic inequalities they rely on taken as premises.
--
--   **Formalization Note** $\mathrm{KappaBound}(\kappa)$ is defined in `IntMul_MultitapeModel`, which uses the $k$-tape Turing machine conventions of Montanaro's lecture notes (start symbol, $\mathrm{HALT}$ state, read-only input tape, separate output tape). It asserts a single machine that, for every $n\ge1$ and all $x,y\in\{0,1\}^n$, halts on input $x\#y$ with output $\operatorname{bin}_{2n}(\operatorname{val}(x)\operatorname{val}(y))$, and whose worst-case running time is at most $c\,n(\lg n)^{1-\kappa}$ for all $n\ge n_0$, for some $c>0$ and $n_0$. Here $\lg n=\max(\lceil\log_2n\rceil,1)$.
-- source:
--   S. Jain, Integer multiplication: a conditional witness above 2^-15 (integer-mult-kappa), research draft, https://github.com/Swapnil-jain/integer-mult-kappa (README headline, Round six; scripts/certificate_round6.py, lean/Round6.lean; commit f2176bc), stated as conditional on OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf and on D. Colkitt, https://github.com/CrocSwap/integer-mult-bounds

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.Kappa

theorem jain_round6 : KappaBound (3666565558019 / 10 ^ 17) := by sorry

end IntMul.Kappa
