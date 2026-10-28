-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_gammaTwo_eq_hessianSqStdBasis_add_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:50.213759+00:00
-- url     : https://prove2.me/theorems/179f18c6-eedc-4764-b606-7f97a6d4c71b
-- title:
--   Standard-Basis Bochner Identity
-- statement:
--   This formalizes the pointwise Bochner identity in the fixed standard orthonormal basis.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $U:E\to\mathbb R$ be $C^2$, let $f:E\to\mathbb R$ be $C^3$, and let $x\in E$. Then
--
--   $$
--   \Gamma_2(U,f)(x)
--   =
--   \operatorname{HessSq}_{\mathrm{std}}(f)(x)
--   +D^2U(x)(\nabla f(x),\nabla f(x)).
--   $$
--
--   Here `gammaTwo U f` is the pointwise carré-du-champ iteration, and `hessianSqStdBasis f x` is the sum of squares of the Hessian entries in the fixed basis $(e_i)$:
--   $\operatorname{HessSq}_{\mathrm{std}}(f)=\sum_{i,j}(D^2f(e_i,e_j))^2$.
--
--   This is the central local identity used to derive nonnegativity and curvature estimates; it asserts a standard-basis formula, not basis independence.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gammaTwo_eq_hessianSqStdBasis_add {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
--       (hf : ContDiff ℝ 3 f) (x : E) :
--       gammaTwo U f x =
--         hessianSqStdBasis f x +
--           bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a).
--
--   Definition modules: [`Analysis/BakryEmery/Gamma`](https://prove2.me/theorems/6b6aef00-0f84-4633-a830-e04239f02b6b).
--
--   Supporting theorems: [`inner_gradient_gradient_inner`](https://prove2.me/theorems/b52d0520-93db-489b-81f1-06d18ce5c1bc), [`inner_gradient_gradient_laplacian`](https://prove2.me/theorems/7d81666e-8540-4388-b49c-344114d6512a), [`laplacian_norm_gradient_sq`](https://prove2.me/theorems/f7c7e14e-684d-4c0f-a364-0f0a923ffcc2).
--
--   Previous: [`inner_gradient_gradient_inner`](https://prove2.me/theorems/b52d0520-93db-489b-81f1-06d18ce5c1bc).
--
--   [Source excerpt, lines 298–302](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L298-L302) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L296-L313 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add_readable {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (x : E) :
    gammaTwo U f x =
      hessianSqStdBasis f x +
        bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) := by sorry
