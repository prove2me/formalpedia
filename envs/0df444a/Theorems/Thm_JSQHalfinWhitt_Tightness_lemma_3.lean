-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_3
-- name    : JSQHalfinWhitt.Tightness.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:09.382288+00:00
-- url     : https://prove2.me/theorems/a370da92-12dc-4333-a47a-7f95ce1da335
-- title:
--   Lemma 3 — generator expansion $G_XAf = Lf + (f_2 - f_1)\lambda 1(x_1 = 0) + \varepsilon$
-- statement:
--   Let $n \ge 1$, $\beta > 0$ with $\beta < \sqrt n$, and $\lambda = 1 - \beta/\sqrt n$. For a state $q \in S$ of the join-the-shortest-queue chain let $x_1 = (q_1 - n)/n$ and $x_2 = q_2/n$. Let $f$ be defined on $\Omega = (-\infty,0]\times[0,\infty)$ with partial derivatives $f_1, f_2$ (one-sided on $\partial\Omega$) such that $f_1(\cdot, y_2)$ and $f_2(y_1, \cdot)$ are absolutely continuous for all $y \in \Omega$, with weak derivatives $f_{11}$ and $f_{22}$. Write $(Af)(q) = f(x_1, x_2)$ and $G_X Af = G_Q(Af)$. Then for all $q \in S$,
--   $$G_X Af(q) = Lf(x) + \big(f_2(x) - f_1(x)\big)\lambda 1(x_1 = 0) + \varepsilon(x),$$
--   where $Lf(x) = (-x_1 + x_2 - \beta/\sqrt n) f_1(x) - x_2 f_2(x)$ and
--   $$\begin{aligned}\varepsilon(x) = {} & -f_2(x)\lambda 1(q_1 = q_2 = n) + q_3 \int_{x_2 - 1/n}^{x_2} f_2(x_1, u)\,du \\ & + n\lambda 1(q_1 < n) \int_{x_1}^{x_1 + 1/n} (x_1 + 1/n - u) f_{11}(u, x_2)\,du \\ & + n\lambda 1(q_1 = n, q_2 < n) \int_{x_2}^{x_2 + 1/n} (x_2 + 1/n - u) f_{22}(x_1, u)\,du \\ & + (q_1 - q_2) \int_{x_1 - 1/n}^{x_1} \big(u - (x_1 - 1/n)\big) f_{11}(u, x_2)\,du \\ & + q_2 \int_{x_2 - 1/n}^{x_2} \big(u - (x_2 - 1/n)\big) f_{22}(x_1, u)\,du. \end{aligned}$$
--
--   The expansion splits the generator of the fluid-scaled chain into the first-order fluid drift $Lf$, a reflection term on the boundary $x_1 = 0$, and an error $\varepsilon$ controlled by second derivatives; it is the bridge between the PDE (3.7)–(3.8) and stationary expectations.
--
--   **Formalization Note** $G_X Af$ is formalized as `genQ` applied to $q \mapsto f(x(q))$, the generator of $Q$ acting on the lifted function, which is how the paper's display on p. 7 arises. The regularity of $f$ is the predicate `IsWeakC2 f f1 f2 f11 f22`: $f_1, f_2$ are one-sided partial derivatives on $\Omega$ and $f_1(\cdot,x_2)$, $f_2(x_1,\cdot)$ are absolutely continuous with a.e. derivatives $f_{11}, f_{22}$. Lean indices are 0-based (`q.1 0, q.1 1, q.1 2` are $q_1, q_2, q_3$). Integrals that reach outside $\Omega$ occur only with a vanishing coefficient. The Halfin–Whitt standing assumptions $\beta > 0$, $\beta < \sqrt n$ are hypotheses; the identity uses $\lambda = 1 - \beta/\sqrt n$ through $L$.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), pp. 7–8, Lemma 3 (G_X Af displayed on p. 7, L in (3.4); proof in App. A.3, p. 22)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Definitions.Def_JSQHalfinWhitt_Tightness_PDE

namespace JSQHalfinWhitt.Tightness

open scoped Classical

/-- Lemma 3 (Braverman, pp. 7–8): the generator expansion. Let `λ = 1 − β/√n` and let
`f` have partial derivatives `f_1, f_2` on `Ω` with `f_1(·, x_2)`, `f_2(x_1, ·)` absolutely
continuous with weak derivatives `f_11`, `f_22`. Then for every state `q`, with
`x = ((q_1 − n)/n, q_2/n)`, `G_X Af(q) = G_Q(f ∘ x)(q)` equals
`Lf(x) + (f_2(x) − f_1(x)) λ 1(x_1 = 0) + ε(x)`, with `ε(x)` the six-term remainder of p. 8.
Lean indices are 0-based: `q.1 0, q.1 1, q.1 2` are `q_1, q_2, q_3`. -/
theorem lemma_3 (n : ℕ) (β : ℝ) (hn : 1 ≤ n) (hβ : 0 < β) (hβn : β < Real.sqrt n)
    (f f1 f2 f11 f22 : ℝ × ℝ → ℝ) (hf : IsWeakC2 f f1 f2 f11 f22) (q : State n) :
    genQ n (lamHW β n) (fun r => f (xOf r)) q =
      Lop β n f1 f2 (xOf q)
        + (f2 (xOf q) - f1 (xOf q)) * lamHW β n * (if (xOf q).1 = 0 then 1 else 0)
        + (-(f2 (xOf q)) * lamHW β n * (if q.1 0 = n ∧ q.1 1 = n then 1 else 0)
          + (q.1 2 : ℝ) * ∫ u in ((xOf q).2 - 1 / n)..(xOf q).2, f2 ((xOf q).1, u)
          + n * lamHW β n * (if q.1 0 < n then 1 else 0) *
              ∫ u in (xOf q).1..((xOf q).1 + 1 / n),
                ((xOf q).1 + 1 / n - u) * f11 (u, (xOf q).2)
          + n * lamHW β n * (if q.1 0 = n ∧ q.1 1 < n then 1 else 0) *
              ∫ u in (xOf q).2..((xOf q).2 + 1 / n),
                ((xOf q).2 + 1 / n - u) * f22 ((xOf q).1, u)
          + ((q.1 0 : ℝ) - q.1 1) *
              ∫ u in ((xOf q).1 - 1 / n)..(xOf q).1,
                (u - ((xOf q).1 - 1 / n)) * f11 (u, (xOf q).2)
          + (q.1 1 : ℝ) *
              ∫ u in ((xOf q).2 - 1 / n)..(xOf q).2,
                (u - ((xOf q).2 - 1 / n)) * f22 ((xOf q).1, u)) := by sorry

end JSQHalfinWhitt.Tightness
