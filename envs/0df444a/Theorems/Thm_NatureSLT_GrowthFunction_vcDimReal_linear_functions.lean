-- Prove2me | Theorems.Thm_NatureSLT_GrowthFunction_vcDimReal_linear_functions
-- name    : NatureSLT.GrowthFunction.vcDimReal_linear_functions
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:34.196396+00:00
-- url     : https://prove2.me/theorems/62acbe76-4088-4706-ace6-733e97c6d60e
-- title:
--   Section 3.6, Example 1(ii) — real linear functions in ℝⁿ have VC dimension n + 1
-- statement:
--   Let $n \ge 0$ and consider the set of real **linear functions** on the $n$-dimensional coordinate space $Z = \mathbb R^n$,
--
--   $$Q(z, \alpha) = \sum_{p=1}^n \alpha_p z_p + \alpha_0, \qquad \alpha_0, \dots, \alpha_n \in (-\infty, \infty).$$
--
--   Its VC dimension as a set of real functions, i.e. the VC dimension of the indicators $\theta\{Q(z, \alpha) - \beta\}$ with $\alpha \in \mathbb R^{n+1}$ and $\beta \in (A, B) = (-\infty, \infty)$, where $\theta(u) = 0$ for $u < 0$ and $\theta(u) = 1$ for $u \ge 0$, is
--
--   $$h = n + 1 .$$
--
--   (Replacing $\alpha_0$ by $\alpha_0 - \beta$ does not change the set of indicator functions, so this is the VC dimension of the linear indicator functions of Example 1(i).)
--
--   **Formalization Note** The bounds of the definition are $A = -\infty$ and $B = +\infty$, so the threshold $\beta$ ranges over all real numbers and the boundedness condition $A \le Q \le B$ is void. Points of $\mathbb R^n$ are elements of `EuclideanSpace ℝ (Fin n)`; indicator values are booleans (`true` = $1$).
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 81, Section 3.6, Example 1(ii)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDimReal

namespace NatureSLT.GrowthFunction

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §3.6, p. 81, Example 1(ii): the
VC dimension of the set of linear functions `Q(z, α) = ∑_{p=1}^n α_p z_p + α₀`,
`α₀, …, α_n ∈ (−∞, ∞)`, in `n`-dimensional coordinate space, is `h = n + 1`. The VC dimension of
real functions is that of the indicators `θ{Q(z, α) − β}`, `β ∈ (A, B)`, here with
`A = −∞`, `B = ∞`. -/
theorem vcDimReal_linear_functions (n : ℕ) :
    vcDimReal (fun (α : (Fin n → ℝ) × ℝ) (z : EuclideanSpace ℝ (Fin n)) =>
      ∑ p : Fin n, α.1 p * z p + α.2) ⊥ ⊤ = ((n + 1 : ℕ) : ℕ∞) := by sorry

end NatureSLT.GrowthFunction
