-- Prove2me | Theorems.Thm_GassSaaty_ParametricPivot_below_lambdaBar_violates_ineq3_prime
-- name    : GassSaaty.ParametricPivot.below_lambdaBar_violates_ineq3_prime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:42:24.176978+00:00
-- url     : https://prove2.me/theorems/9082c63a-7181-4ed9-8a5f-649a96a0c2b9
-- title:
--   Proof of the THEOREM, (7)–(8) — no $\lambda < \bar\lambda$ satisfies (3') for the new basis
-- statement:
--   Let $B$ be a basis, $s$ an index with $\beta_s > 0$, $r = B(\ell)$ a basic column with $y_{rs} > 0$, and $B'$ the basis obtained by bringing $A_s$ in and taking $A_r$ out. Put $\bar\lambda = -\alpha_s/\beta_s$. Then no $\lambda < \bar\lambda$ satisfies the inequalities (3') of the new basis:
--
--   $$
--   \lambda < \bar\lambda \ \Longrightarrow\ \text{not } \big(\alpha'_j + \lambda\beta'_j \le 0 \text{ for all } j = 1,\dots,n\big).
--   $$
--
--   The violated inequality is the one for the leaving column $j = r$: by (7), $\alpha'_r + \lambda\beta'_r = -(\alpha_s + \lambda\beta_s)/y_{rs}$, which is positive since $y_{rs} > 0$, $\beta_s > 0$ and $\alpha_s + \bar\lambda\beta_s = 0$.
--
--   **Printed slip.** The paper derives from $\alpha'_r + \beta'_r\lambda \le 0$ for $\lambda < \bar\lambda$ the inequality "(8) $\alpha_s + \beta_s\lambda \le 0$ for $\lambda < \bar\lambda$" and declares it contradicted. With $y_{rs} > 0$ the correct consequence is $\alpha_s + \beta_s\lambda \ge 0$, and it is this inequality that contradicts $\beta_s > 0$, $\alpha_s + \beta_s\bar\lambda = 0$; the printed (8) is true for $\lambda < \bar\lambda$. The statement here is the conclusion of the corrected argument, which is the paper's claim "$\lambda < \bar\lambda$ does not satisfy (3')".
--
--   **Formalization Note** $\lambda$ is the Lean variable `t`. Only $\beta_s > 0$ and $y_{rs} > 0$ are needed; whether $s$ attains the minimum in (5) plays no role in this step.
-- source:
--   Gass and Saaty, The computational algorithm for the parametric objective function, Naval Res. Logist. Quart. 2 (1955), p. 41, proof of the THEOREM, Eqs. (6)–(8) (printed (8) corrected)

import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem below_lambdaBar_violates_ineq3_prime {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    ∀ t : ℝ, t < -alpha A d B s / beta A d' B s →
      ¬ ∀ j, alpha A d B' j + t * beta A d' B' j ≤ 0 := by sorry

end GassSaaty.ParametricPivot
