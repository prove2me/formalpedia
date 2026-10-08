-- Prove2me | Theorems.Thm_OffloadGNEP_Exist_partial_gradient_eq_F
-- name    : OffloadGNEP.Exist.partial_gradient_eq_F
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:41.487807+00:00
-- url     : https://prove2.me/theorems/83708dc6-db22-4688-81a8-6fe6b9a2609c
-- title:
--   p. 11, definition of F — F stacks the partial gradients ∇_{x_u} λ_uR_u of the users' costs
-- statement:
--   Assume Assumption A and the standing hypotheses. Fix a user $u$ and a profile $x$ with $1-\alpha_ux_{u,m}>0$ and $D(x)=1-\frac1n\sum_v\delta_vx_{v,\mathrm{clet}}>0$. Then the map $y\mapsto\lambda_uR_u(y,x_{-u})$ on $\mathbb R^3$ is (Fréchet) differentiable at $y=x_u$, and its gradient is the $u$-th block of $F$:
--   $$\nabla_{x_u}\lambda_uR_u(x)=\Big(\frac{\alpha_u}{(1-\alpha_ux_{u,m})^2},\ \beta_u+\delta_u\frac{1-\frac1n\sum_{v\ne u}\delta_vx_{v,\mathrm{clet}}}{\big(1-\frac1n\sum_v\delta_vx_{v,\mathrm{clet}}\big)^2},\ \gamma_u\Big)^\top=F(x)_u.$$
--
--   This is what makes $F$ the map of the variational inequality associated with the jointly convex game: $\mathrm{VI}(K,F)$ collects the first-order conditions of all users at once.
--
--   **Formalization Note** $F$ is defined by its closed form, so this statement is not definitional. The derivative is the linear form $h\mapsto\sum_{i\in I}F(x)_{u,i}h_i$ on `Tier → ℝ`. The two strict inequalities define an open set containing $K$, on which the cost formula has no division by zero.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 11, definition of F (display of ∇_{x_u}λ_uR_u and F)

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

namespace OffloadGNEP.Exist

/-- p. 11, definition of `F`: the `u`-th block of `F` is the partial gradient of user `u`'s
objective `λ_u R_u(·, x_{-u})` with respect to its own variables `x_u`. Stated at every profile `x`
with `1 - α_u x_{u,m} > 0` and `1 - (1/n)∑_v δ_v x_{v,clet} > 0`, an open set containing `K` on
which the closed form of `cost` has no junk division. The derivative is the linear form
`h ↦ ∑_i F(x)_{u,i} h_i` on `ℝ³ = Tier → ℝ`. -/
theorem partial_gradient_eq_F {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (u : Fin N) (x : Fin N → Tier → ℝ) (hm : P.alpha u * x u .m < 1) (hD : load P x < 1) :
    HasFDerivAt (fun y : Tier → ℝ => cost P u (Function.update x u y))
      (∑ i : Tier, F P x u i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Tier => ℝ) i)
      (x u) := by sorry

end OffloadGNEP.Exist
