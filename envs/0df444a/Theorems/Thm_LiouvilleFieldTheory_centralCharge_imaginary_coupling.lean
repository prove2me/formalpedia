-- Prove2me | Theorems.Thm_LiouvilleFieldTheory_centralCharge_imaginary_coupling
-- name    : LiouvilleFieldTheory.centralCharge_imaginary_coupling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T10:17:48.534792+00:00
-- url     : https://prove2.me/theorems/072edb02-2cdf-46dd-acc3-d0328cb9a123
-- title:
--   Imaginary coupling $\beta = ib \in \mathbb{R}$ gives exactly $c \le 1$
-- statement:
--   Write the coupling constant as $b = -i\beta$, i.e. $\beta = ib$. As $\beta$ ranges over the nonzero real numbers, the central charge $c = 1 + 6(b + 1/b)^2$ ranges exactly over the real numbers $c \le 1$:
--   $$\left\{\, 1 + 6\left(b + \tfrac1b\right)^2 \;:\; b = -i\beta,\ \beta \in \mathbb{R}\setminus\{0\} \right\} \;=\; (-\infty, 1] \subset \mathbb{C}.$$
--
--   In the source, the three-point structure constant for $c \in (-\infty, 1)$ is written in terms of $\beta = ib \in \mathbb{R}$; this statement records that real $\beta$ covers that range of central charges, and in fact produces exactly $c \in (-\infty, 1]$ (the value $c = 1$ occurs at $\beta = \pm 1$).
--
--   **Formalization Note** Real numbers $c \le 1$ are encoded as complex numbers with zero imaginary part and real part at most $1$.
-- source:
--   Wikipedia, "Liouville field theory", revision oldid=1376996606 (https://en.wikipedia.org/w/index.php?title=Liouville_field_theory&oldid=1376996606); section Correlation functions and DOZZ formula (p. 3): "For c ∈ (−∞, 1), the three-point structure constant is ... where β = ib ∈ ℝ".

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex

namespace LiouvilleFieldTheory

theorem centralCharge_imaginary_coupling :
    {c : ℂ | ∃ β : ℝ, β ≠ 0 ∧ centralCharge (-I * β) = c} =
      {c : ℂ | c.im = 0 ∧ c.re ≤ 1} := by
  sorry

end LiouvilleFieldTheory
