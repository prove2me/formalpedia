-- Prove2me | Theorems.Thm_IntMul_Kappa_colkitt_2pow30
-- name    : IntMul.Kappa.colkitt_2pow30
-- status  : Open
-- author  : @avi
-- created : 2026-10-08T17:48:41.680972+00:00
-- url     : https://prove2.me/theorems/f3fa305a-7e84-4fb6-8e0f-fa764e12f288
-- title:
--   Colkitt — multiplication in time $O(n(\lg n)^{1-\kappa})$, $\kappa=2^{-30}$
-- statement:
--   **Colkitt's $2^{-30}$ checkpoint.** In the fixed finite-alphabet Turing-machine model with a fixed number of one-dimensional tapes, two $n$-bit integers can be multiplied exactly in time
--   $$T(n)=O\big(n(\lg n)^{1-\kappa}\big),\qquad\kappa=2^{-30}.$$
--
--   The integer-mult-bounds project claims this by patching the OpenAI manuscript: a ternary five-subset interchange circuit with rational address frames and a fixed-alphabet interchange recurrence, certified by exact rational margins. The project states that the claim is conditional on the upstream manuscript and has not had independent review.
--
--   **Formalization Note** $\mathrm{KappaBound}(\kappa)$ is defined in `IntMul_MultitapeModel`, which uses the $k$-tape Turing machine conventions of Montanaro's lecture notes (start symbol, $\mathrm{HALT}$ state, read-only input tape, separate output tape). It asserts a single machine that, for every $n\ge1$ and all $x,y\in\{0,1\}^n$, halts on input $x\#y$ with output $\operatorname{bin}_{2n}(\operatorname{val}(x)\operatorname{val}(y))$, and whose worst-case running time is at most $c\,n(\lg n)^{1-\kappa}$ for all $n\ge n_0$, for some $c>0$ and $n_0$. Here $\lg n=\max(\lceil\log_2n\rceil,1)$.
-- source:
--   D. Colkitt, A sharper exponent for integer multiplication (integer-mult-bounds), research draft, https://github.com/CrocSwap/integer-mult-bounds (README headline T(n)=O(n(log n)^{1-kappa}), kappa=2^-30; ternary-30 patch and artifacts/ternary-note.pdf; commit 1a74950), stated as conditional on OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.Kappa

theorem colkitt_2pow30 : KappaBound (1 / 2 ^ 30) := by sorry

end IntMul.Kappa
