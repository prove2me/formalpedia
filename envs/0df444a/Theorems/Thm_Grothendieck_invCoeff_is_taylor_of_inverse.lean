-- Prove2me | Theorems.Thm_Grothendieck_invCoeff_is_taylor_of_inverse
-- name    : Grothendieck.invCoeff_is_taylor_of_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T16:19:43.473064+00:00
-- url     : https://prove2.me/theorems/f3fb25a3-0304-4c67-ab03-fbbff28402ba
-- title:
--   $b_j$ are the Taylor coefficients of $E_r^{-1}$, and $E_r$ of the series is the identity
-- statement:
--   Write $b_j$ for the Taylor coefficients of the paper's inverse function, encoded as
--   `b_j = (E_r^{-1})^{(j)}(0)/j!`, and let $E_r^{-1}$ be the inverse of $E_r$ on $[-1,1]$. This node
--   establishes that those coefficients really are the Taylor coefficients of that inverse:
--
--   $$E_r^{-1}(y)=\sum_{n\ge0}b_n\,y^n \quad\text{for } y \text{ near } 0,\qquad\text{and}\qquad E_r\Big(\sum_{n\ge0}b_n\,y^n\Big)=y \quad\text{near } 0,$$
--
--   together with the analyticity of $E_r^{-1}$ at the origin.
--
--   The argument is short and uses only analyticity. With $\Psi(u)=\sum_k a_k u^k$ (the coefficients of $E_r$ at odd powers), one has $E_r(t)=t\,\Psi(t^2)$, so $E_r$ is analytic at $0$ with $E_r'(0)=\Psi(0)=C_r\ne0$; Mathlib's analytic inverse-function theorem gives an analytic local inverse; that local inverse coincides with `ErInv` near $0$ because both are right inverses of $E_r$ there and $E_r$ is injective on $[-1,1]$; and the power series of an analytic function has coefficients $f^{(n)}(0)/n!$, which is the definition of $b_n$.
--
--   Why it matters is formal rather than mathematical: without it, any argument about $\sum_j b_j(t\beta)^j$ has to unfold `Function.invFunOn` and `iteratedDeriv`. With it, Proposition 4.2 reduces to a statement about a convergent power series, and Lemma 3.2's contour representation can be matched against the same coefficients.
--
--   **Formalization Note** Stated over $\mathbb{R}$ near $0$; the complex analogue is still owed. A supporting lemma, not a verbatim statement of the paper.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — equation (3.1), p. 88 (the Taylor expansion of $E_r^{-1}$) and Proposition 4.2, p. 92.

import Mathlib
import Definitions.Def_Grothendieck_Series

open Filter
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **`invCoeff` are the Taylor coefficients of the genuine inverse.** `ErInv r` is real-analytic at
`0`, its power series there is `Σ_n invCoeff r n · y^n`, and composing with `E_r` gives the identity
on a neighbourhood of `0`. -/
theorem invCoeff_is_taylor_of_inverse (r : ℕ) (hr : 1 ≤ r) :
    AnalyticAt ℝ (ErInv r) 0 ∧
      (∀ᶠ y in 𝓝 (0:ℝ), HasSum (fun n : ℕ => invCoeff r n * y ^ n) (ErInv r y)) ∧
      (∀ᶠ y in 𝓝 (0:ℝ), Er r (∑' n : ℕ, invCoeff r n * y ^ n) = y) := by sorry

end Grothendieck
