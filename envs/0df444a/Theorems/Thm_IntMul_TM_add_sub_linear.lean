-- Prove2me | Theorems.Thm_IntMul_TM_add_sub_linear
-- name    : IntMul.TM.add_sub_linear
-- status  : Proved
-- author  : @avi
-- created : 2026-10-09T02:08:38.626064+00:00
-- url     : https://prove2.me/theorems/02ee99a6-3049-4d13-a20d-ec092f55e29c
-- title:
--   Addition and subtraction of $n$-bit integers in time $O(n)$ on a multitape Turing machine
-- statement:
--   **Addition and subtraction in linear time.** Both of the following hold.
--
--   1. **Addition.** There are a deterministic multitape Turing machine $M$ and a constant $c>0$ such that for every $n\ge0$ and all $x,y\in\{0,1\}^n$, on input $x\#y$ the machine halts within $c\,(n+1)$ steps with output
--   $$\operatorname{bin}_{n+1}\big(\operatorname{val}x+\operatorname{val}y\big),$$
--   the exact sum written with $n+1$ bits, most significant first.
--
--   2. **Subtraction.** There are a deterministic multitape Turing machine $M'$ and a constant $c'>0$ such that for every $n\ge0$ and all $x,y\in\{0,1\}^n$, on input $x\#y$ the machine halts within $c'(n+1)$ steps with the $(n+1)$-bit output
--   $$s\;\operatorname{bin}_n\big(|\operatorname{val}x-\operatorname{val}y|\big),\qquad s=\begin{cases}1&\text{if }\operatorname{val}x<\operatorname{val}y,\\0&\text{otherwise,}\end{cases}$$
--   that is, a sign bit followed by the $n$-bit magnitude of the difference (zero has sign $0$).
--
--   These are the linear-time integer operations quoted in §2.1 of Harvey–van der Hoeven ("we may compute $x+y$ and $x-y$ in time $O(n)$"), here for operands of equal bit length $n$, in sign-and-magnitude form.
--
--   **Formalization Note** The machine model is the shared `IntMul_MultitapeModel` with input $x\#y$. The bounds hold for every $n$, including $n=0$ (input $\#$); nothing is required on inputs with $|x|\ne|y|$. The two parts may use different machines.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), §2.1, p. 8: 'We may compute x + y and x − y in time O(n)' (citing Brent–Zimmermann, Modern Computer Arithmetic, 2011, Ch. 1, §1.2).

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.TM

theorem add_sub_linear :
    (∃ M : MultitapeTM, ∃ c : ℝ, 0 < c ∧ ∀ x y : List Bool, x.length = y.length →
      ∃ t : ℕ, (t : ℝ) ≤ c * (x.length + 1) ∧
        M.HaltsWithOutput x y t (bin (x.length + 1) (val x + val y))) ∧
    (∃ M : MultitapeTM, ∃ c : ℝ, 0 < c ∧ ∀ x y : List Bool, x.length = y.length →
      ∃ t : ℕ, (t : ℝ) ≤ c * (x.length + 1) ∧
        M.HaltsWithOutput x y t
          (decide (val x < val y) ::
            bin x.length (if val y ≤ val x then val x - val y else val y - val x))) := by sorry

end IntMul.TM
