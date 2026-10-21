-- Prove2me | Theorems.Thm_NatureSLT_GrowthFunction_vcDim_linear_indicators
-- name    : NatureSLT.GrowthFunction.vcDim_linear_indicators
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:46.798231+00:00
-- url     : https://prove2.me/theorems/ab5f32a4-befd-4a4b-9429-52fce4514263
-- title:
--   Section 3.6, Example 1(i) — linear indicator functions in ℝⁿ have VC dimension n + 1
-- statement:
--   Let $n \ge 0$ and consider the set of **linear indicator functions** on the $n$-dimensional coordinate space $Z = \mathbb R^n$, $z = (z_1, \dots, z_n)$,
--
--   $$Q(z, \alpha) = \theta\left\{\sum_{p=1}^n \alpha_p z_p + \alpha_0\right\}, \qquad \alpha = (\alpha_1, \dots, \alpha_n, \alpha_0) \in \mathbb R^{n+1},$$
--
--   where $\theta(u) = 0$ for $u < 0$ and $\theta(u) = 1$ for $u \ge 0$. Its VC dimension (the maximum number of vectors it shatters) is
--
--   $$h = n + 1 .$$
--
--   The VC dimension here equals the number of free parameters $\alpha_0, \alpha_1, \dots, \alpha_n$; Example 2 shows that this is not true in general.
--
--   **Formalization Note** The closed half-space convention $\theta(0) = 1$ of the book is kept (a point on the hyperplane gets the value $1$). Points of $\mathbb R^n$ are elements of `EuclideanSpace ℝ (Fin n)`, coordinates indexed from $0$; indicator values are booleans (`true` = $1$).
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 81, Section 3.6, Example 1(i)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_NatureSLT_GrowthFunction_stepFunction

namespace NatureSLT.GrowthFunction

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §3.6, p. 81, Example 1(i): the
VC dimension of the set of linear indicator functions
`Q(z, α) = θ{∑_{p=1}^n α_p z_p + α₀}` in `n`-dimensional coordinate space `Z = (z₁, …, z_n)` is
`h = n + 1`. The parameter is `α = ((α₁, …, α_n), α₀) ∈ ℝⁿ × ℝ` (coordinates indexed from `0`),
and `θ(0) = 1`. -/
theorem vcDim_linear_indicators (n : ℕ) :
    vcDim (fun (α : (Fin n → ℝ) × ℝ) (z : EuclideanSpace ℝ (Fin n)) =>
      stepFunction (∑ p : Fin n, α.1 p * z p + α.2)) = ((n + 1 : ℕ) : ℕ∞) := by sorry

end NatureSLT.GrowthFunction
