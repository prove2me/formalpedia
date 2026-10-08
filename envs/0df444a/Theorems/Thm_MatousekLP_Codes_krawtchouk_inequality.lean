-- Prove2me | Theorems.Thm_MatousekLP_Codes_krawtchouk_inequality
-- name    : MatousekLP.Codes.krawtchouk_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:13:16.194354+00:00
-- url     : https://prove2.me/theorems/d470a3ba-65df-44e5-a5d1-28f52de51794
-- title:
--   Proposition 8.4.4 — $\sum_{i=0}^n K_t(n,i)\,\tilde x_i(C) \ge 0$
-- statement:
--   Let $C \subseteq \{0,1\}^n$ be an arbitrary set of words, let
--   $$
--   \tilde x_i = \tilde x_i(C) = \frac{1}{|C|}\bigl|\{(\mathbf w,\mathbf w') \in C^2 : d_H(\mathbf w,\mathbf w') = i\}\bigr|, \qquad i = 0,\dots,n,
--   $$
--   and let $t \in \{1,\dots,n\}$. Then, with the Krawtchouk numbers $K_t(n,i) = \sum_{j=0}^{\min(i,t)}(-1)^j\binom ij\binom{n-i}{t-j}$,
--   $$
--   \sum_{i=0}^n K_t(n,i)\,\tilde x_i \;\ge\; 0 .
--   $$
--
--   These are exactly the nontrivial constraints of the Delsarte linear program; together with the easy constraints they show that $(\tilde x_0,\dots,\tilde x_n)$ is feasible whenever $C$ is a code with distance $d$.
--
--   **Formalization Note** $C$ may be empty, in which case Lean's $1/0 = 0$ makes every $\tilde x_i$ zero and the inequality reads $0 \ge 0$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, pp. 160–161, Proposition 8.4.4

import Mathlib
import Definitions.Def_MatousekLP_Codes_Basic
import Definitions.Def_MatousekLP_Codes_DelsarteLP

open Finset

namespace MatousekLP.Codes

/-- Proposition 8.4.4, pp. 160–161: for an arbitrary `C ⊆ {0,1}^n` and every
`t ∈ {1, …, n}`, `∑_{i=0}^n K_t(n, i) · x̃_i(C) ≥ 0`. -/
theorem krawtchouk_inequality {n : ℕ} (C : Finset (Word n)) (t : ℕ) (ht1 : 1 ≤ t)
    (htn : t ≤ n) :
    0 ≤ ∑ i ∈ Finset.range (n + 1), (K n t i : ℝ) * xtilde C i := by sorry

end MatousekLP.Codes
