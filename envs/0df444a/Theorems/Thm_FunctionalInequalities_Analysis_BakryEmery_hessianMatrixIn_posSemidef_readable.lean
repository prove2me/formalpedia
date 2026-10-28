-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_hessianMatrixIn_posSemidef_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn_posSemidef_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:01.304005+00:00
-- url     : https://prove2.me/theorems/058f9921-bf17-4a55-978b-a367731b240a
-- title:
--   Positive Semidefinite Hessian Matrix
-- statement:
--   This theorem converts pointwise nonnegativity of a Hessian bilinear form into positive semidefiniteness of its matrix in an orthonormal basis.
--
--   Let $E$ be a real inner-product space, let $b$ be an orthonormal basis indexed by $\operatorname{Fin}(m)$, and let $\phi:E\to\mathbb R$. At $x\in E$, assume that $\phi$ is twice continuously differentiable and that
--
--   $$0\le D^2\phi(x)[v,v]\qquad\text{for every }v\in E.$$
--
--   Then the matrix `hessianMatrixIn φ b x` is positive semidefinite:
--
--   $$\operatorname{PosSemidef}(\operatorname{hessianMatrixIn}(\phi,b,x)).$$
--
--   This is a pointwise linear-algebraic bridge between the Hessian form and its coordinate matrix.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hessianMatrixIn_posSemidef {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
--       {φ : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x)
--       (hH : ∀ v : E, 0 ≤ bilinearIteratedFDerivTwo ℝ φ x v v) :
--       (hessianMatrixIn φ b x).PosSemidef
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/MongeAmpere`](https://prove2.me/theorems/2b5c2043-7539-4080-9bb7-264ef25c0839).
--
--   [Source excerpt, lines 219–222](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/MongeAmpere.lean#L219-L222) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/MongeAmpere.lean#L217-L241 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.MongeAmpere`, declaration `FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn_posSemidef`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn_posSemidef_readable {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x)
    (hH : ∀ v : E, 0 ≤ bilinearIteratedFDerivTwo ℝ φ x v v) :
    (hessianMatrixIn φ b x).PosSemidef := by sorry
