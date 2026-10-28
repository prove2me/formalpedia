-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_norm_coordTensor_taylorTensor_sq_le_of_smooth_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_of_smooth_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:44.450368+00:00
-- url     : https://prove2.me/theorems/ad272b35-4fb6-4f10-b3ea-e0b98ec982a2
-- title:
--   Extension of Normalized Smooth Taylor Bounds to Affine-Orthogonal $L^2$ Functions
-- statement:
--   This auxiliary extension statement formalizes a component of Proposition 7.1, p. 28, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), rather than the full proposition.
--
--   Let $d,n\in\mathbb N$, $b\ge0$, and $V:\mathbb R^n\to\mathbb R$. Suppose $h_V:$ `RegularPotential` $V\ a\ b'$: $a,b'>0$, $V$ is smooth with derivatives of polynomial growth, and $a\operatorname{Id}\le D^2V\le b'\operatorname{Id}$. Let $\mu=h_V.\text{law}$, the normalized $e^{-V}$ law, and assume it is isotropic (`KLS.Isotropic`). The Euclidean space is `EuclideanSpace ℝ (Fin n)`.
--
--   Write $A_d(h)=\operatorname{coord}(T_d^\mu h)$, using `taylorTensor` and `coordTensor` in the standard orthonormal basis. Assume that every real-valued $g\in C^2\cap L^2(\mu)$ with a globally bounded second Fréchet derivative, $\int g\,d\mu=0$, $\int g^2\,d\mu=1$, and $\int\langle u,x\rangle g(x)\,d\mu=0$ for all $u$, satisfies $\|A_d(g)\|^2\le b/(d!)^2$.
--
--   Then every $f\in L^2(\mu)$ with $\int f\,d\mu=0$ and $\int\langle u,x\rangle f(x)\,d\mu=0$ for all $u$ satisfies
--   $$
--   \|A_d(f)\|^2\le\frac{b}{(d!)^2}\left(\operatorname{toReal}\bigl(\|f\|_{2,\mu}^{\mathrm{ext}}\bigr)\right)^2.
--   $$
--
--   Here the extended norm is `eLpNorm`, valued in $[0,\infty]$. This is a conditional extension from the stated normalized smooth estimate; no cumulant bound or universal KLS bound is asserted. All natural degrees $d$, including $0$, are allowed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_coordTensor_taylorTensor_sq_le_of_smooth {d : ℕ} {b : ℝ} (hb : 0 ≤ b) {n : ℕ}
--       (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
--       (hiso : KLS.Isotropic hV.law)
--       (h113 : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 g →
--         (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M) → MemLp g 2 (hV.law : Measure _) →
--         ∫ x, g x ∂(hV.law : Measure _) = 0 →
--         ∫ x, g x ^ 2 ∂(hV.law : Measure _) = 1 →
--         (∀ u, ∫ x, ⟪u, x⟫ * g x ∂(hV.law : Measure _) = 0) →
--         ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) g d)‖ ^ 2 ≤
--           b / (d.factorial : ℝ) ^ 2)
--       {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (hV.law : Measure _))
--       (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0)
--       (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
--       ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
--         b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/TaylorBound`](https://prove2.me/theorems/ef8651c6-ddf2-4f86-883a-e9e4c00f2d13).
--
--   Definition modules: [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342).
--
--   Selected supporting theorems: [`exists_norm_coordTensor_taylorTensor_le`](https://prove2.me/theorems/f14f3dc2-aea1-4b21-93e6-8c5ccce91407), [`taylorTensor_add`](https://prove2.me/theorems/2ed3b61d-3daf-4e91-b963-da93092fcaf2), [`taylorTensor_const_mul`](https://prove2.me/theorems/7da0a874-3260-449d-b383-221740a01959), [`integrable_exp_mul_norm`](https://prove2.me/theorems/648161d3-ee7c-4a57-800c-c9037b227a1d), [`contDiff_affineOrthPart`](https://prove2.me/theorems/222184b2-bf0f-4088-b7b6-1869ba885db6).
--
--   Next: [`norm_coordTensor_taylorTensor_sq_le_two_mul`](https://prove2.me/theorems/b022259f-6e00-41ce-bbc5-b1bff64f4b1e).
--
--   [Source excerpt, lines 387–401](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/TaylorBound.lean#L387-L401) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/TaylorBound.lean#L385-L458 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.TaylorBound`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_of_smooth`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_TaylorBound

open FunctionalInequalities.Analysis.Tensor
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.L2
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery

theorem FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_of_smooth_readable {d : ℕ} {b : ℝ} (hb : 0 ≤ b) {n : ℕ}
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
    (hiso : KLS.Isotropic hV.law)
    (h113 : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 g →
      (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M) → MemLp g 2 (hV.law : Measure _) →
      ∫ x, g x ∂(hV.law : Measure _) = 0 →
      ∫ x, g x ^ 2 ∂(hV.law : Measure _) = 1 →
      (∀ u, ∫ x, ⟪u, x⟫ * g x ∂(hV.law : Measure _) = 0) →
      ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) g d)‖ ^ 2 ≤
        b / (d.factorial : ℝ) ^ 2)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2 := by sorry
