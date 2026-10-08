-- Prove2me | Theorems.Thm_MatousekLP_Codes_xtilde_feasible
-- name    : MatousekLP.Codes.xtilde_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:13:30.969863+00:00
-- url     : https://prove2.me/theorems/42b9022d-93ee-4d85-93f1-746963b7ace0
-- title:
--   §8.4, p. 160 — the distance distribution $\tilde x(C)$ sums to $|C|$ and is feasible for the Delsarte LP
-- statement:
--   For every code $C \subseteq \{0,1\}^n$, the quantities $\tilde x_i(C) = \frac{1}{|C|}|\{(\mathbf w,\mathbf w') \in C^2 : d_H(\mathbf w,\mathbf w') = i\}|$ satisfy
--   $$
--   \tilde x_0 + \tilde x_1 + \dots + \tilde x_n = |C|,
--   $$
--   and whenever $C$ is a nonempty code with distance $d$, the vector $(\tilde x_0,\dots,\tilde x_n)$ is a feasible solution of the Delsarte linear program:
--   $\tilde x_0 = 1$, $\tilde x_i = 0$ for $i = 1,\dots,d-1$, $\sum_{i=0}^n K_t(n,i)\tilde x_i \ge 0$ for $t = 1,\dots,n$, and $\tilde x_i \ge 0$ for all $i$.
--
--   This is the step that turns a code into a feasible solution of the linear program, from which the Delsarte bound follows.
--
--   **Formalization Note** The book's $\tilde x_i$ divides by $|C|$ and its claim $\tilde x_0 = 1$ presupposes $C \ne \emptyset$; the hypothesis `C.Nonempty` makes this explicit. The identity $\sum_i \tilde x_i = |C|$ holds (trivially) for the empty code as well and is stated under the same hypothesis.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 160, §8.4 'Toward an explanation' (x̃_0 + ⋯ + x̃_n = |C|; the x̃_i are feasible for the LP of Theorem 8.4.3)

import Mathlib
import Definitions.Def_MatousekLP_Codes_Basic
import Definitions.Def_MatousekLP_Codes_DelsarteLP

open Finset

namespace MatousekLP.Codes

/-- §8.4, p. 160 ("Toward an explanation"): for every `C ⊆ {0,1}^n`,
`x̃_0(C) + ⋯ + x̃_n(C) = |C|`; and whenever `C` is a (nonempty) code with distance `d`, the
vector `(x̃_0(C), …, x̃_n(C))` is a feasible solution of the Delsarte linear program. -/
theorem xtilde_feasible {n d : ℕ} (C : Finset (Word n)) (hC : C.Nonempty)
    (hd : HasDistance C d) :
    delsarteObjective (fun i : Fin (n + 1) => xtilde C i) = (C.card : ℝ) ∧
      IsDelsarteFeasible n d (fun i : Fin (n + 1) => xtilde C i) := by sorry

end MatousekLP.Codes
