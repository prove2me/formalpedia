-- Prove2me | Theorems.Thm_NaiveFS_Multinomial_claim_rho_indicator
-- name    : NaiveFS.Multinomial.claim_rho_indicator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:06.692261+00:00
-- url     : https://prove2.me/theorems/1d0dff44-4789-4430-b1ee-3cdf71d0eb89
-- title:
--   Proof of Theorem 3.6, p. 10 — the convex envelope of 1_{x≠y} on [0,1]² is |x − y| and ρ(1_{x≠y}) = 1
-- statement:
--   Let $F:\mathbb R^2\to\mathbb R\cup\{+\infty\}$ be the indicator of disagreement on the unit square,
--   $$F(x,y)=\begin{cases}\mathbf 1_{x\ne y}&(x,y)\in[0,1]^2,\\+\infty&\text{otherwise.}\end{cases}$$
--   Then its biconjugate (convex envelope) satisfies $F^{**}(x,y)=|x-y|$ on $[0,1]^2$, and its lack of convexity is
--   $$\rho(F)=\sup_{x,y\in[0,1]}\big\{\mathbf 1_{y\ne x}-|x-y|\big\}=1.$$
--
--   This is the only nonconvex constraint function in the perturbation form (25) of the sparse problem, so it fixes $\bar p=(0,0,4)$ in Theorem 3.5 and hence the shift $k+4$ in Theorem 3.6.
--
--   **Formalization Note** The supremum defining $\rho(F)$ is not attained; the statement is about its value.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, p. 10, proof of Theorem 3.6, claim ρ(1_{x≠y}) = 1

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_DualityGap

namespace NaiveFS.Multinomial

/-- Proof of Theorem 3.6, p. 10: let `F(x, y) = 1_{x ≠ y}` on `[0,1]²` and `+∞` outside. Its
convex envelope on `[0,1]²` is `|x − y|`, and its lack of convexity is
`ρ(1_{x≠y}) = sup_{x,y∈[0,1]} {1_{y≠x} − |x − y|} = 1`. -/
theorem claim_rho_indicator :
    let F : (Fin 2 → ℝ) → EReal := fun p =>
      if ∀ j, 0 ≤ p j ∧ p j ≤ 1 then (if p 0 ≠ p 1 then 1 else 0) else ⊤
    (∀ p : Fin 2 → ℝ, (∀ j, 0 ≤ p j ∧ p j ≤ 1) → biconj F p = ((|p 0 - p 1| : ℝ) : EReal)) ∧
      lackOfConvexity F = 1 := by sorry

end NaiveFS.Multinomial
