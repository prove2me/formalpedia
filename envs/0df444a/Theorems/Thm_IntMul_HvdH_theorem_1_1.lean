-- Prove2me | Theorems.Thm_IntMul_HvdH_theorem_1_1
-- name    : IntMul.HvdH.theorem_1_1
-- status  : Open
-- author  : @avi
-- created : 2026-10-08T17:37:25.132814+00:00
-- url     : https://prove2.me/theorems/5d267b45-b9ed-45e8-b36a-7450896bf80d
-- title:
--   Theorem 1.1 — integer multiplication in time $O(n\log n)$
-- statement:
--   **Theorem 1.1 of Harvey–van der Hoeven, as stated.** There is an integer multiplication algorithm achieving
--   $$\mathsf M(n)=O(n\log n).$$
--
--   Here $\mathsf M(n)$ is the worst-case number of steps a deterministic multitape Turing machine needs to multiply two $n$-bit integers, and $\log$ is the natural logarithm. Concretely, there is one deterministic multitape Turing machine $M$, with a fixed finite alphabet and a fixed finite number of tapes, with two properties:
--
--   1. For every $n\ge1$ and all $x,y\in\{0,1\}^n$, on input $x\#y$ it halts with output $\operatorname{bin}_{2n}(\operatorname{val}(x)\operatorname{val}(y))$.
--   2. There are constants $c>0$ and $n_0$ such that, for all $n\ge n_0$, it takes at most $c\,n\log n$ steps on every pair of $n$-bit inputs.
--
--   This settles the upper bound in the 1971 conjecture of Schönhage and Strassen that integer multiplication has complexity $\Theta(n\log n)$ in this model.
--
--   **Formalization Note** The bound is $n\log n$ with the natural logarithm, as in the paper, and $O(\cdot)$ has the usual meaning of a bound for all sufficiently large $n$, as in the paper's introduction. Since $\log 1=0$, a valid threshold has $n_0\ge2$. The paper does not fix tape conventions or an input and output format, so the machine model is the shared `IntMul_MultitapeModel`, which uses the $k$-tape conventions of Montanaro's lecture notes with the input $x\#y$ of the OpenAI preprint. The same theorem, stated in the $\kappa$-framework of the companion missions, is the milestone $\mathrm{KappaBound}(0)$.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021) 563-617, https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §1, Theorem 1.1, p. 1 (multitape Turing model and O-notation as stated in §1)

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.HvdH

theorem theorem_1_1 : MulTimeBound fun n => (n : ℝ) * Real.log n := by sorry

end IntMul.HvdH
