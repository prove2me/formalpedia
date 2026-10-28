-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_norm_coordTensor_taylorTensor_sq_le_two_mul_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_two_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:27.798908+00:00
-- url     : https://prove2.me/theorems/b022259f-6e00-41ce-bbc5-b1bff64f4b1e
-- title:
--   Taylor Tensor Bound for Isotropic Regular Laws
-- statement:
--   Let $d\in\mathbb N$ satisfy $2\le d$, let $b\in\mathbb R$ satisfy $0<b$, and assume `CumulantBound d b`. Let $n\in\mathbb N$, let $V:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin} n)\to\mathbb R$, and let $a,b'\in\mathbb R$ be such that `hV : KLS.RegularPotential V a b'`. Assume that the probability law $\mu=\operatorname{law}(hV)$ is isotropic. For every function $f:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin} n)\to\mathbb R$ with $f\in L^2(\mu)$, the coordinate tensor of the $d$-th Taylor tensor satisfies
--
--   $$
--   \left\|\operatorname{coordTensor}(e,\operatorname{taylorTensor}(\mu,f,d))\right\|^2
--   \le \frac{2b}{(d!)^2}\,\bigl(\operatorname{eLpNorm}(f,2,\mu).\operatorname{toReal}\bigr)^2,
--   $$
--
--   where $e$ is the standard basis of $\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin} n)$.
--
--   This is the assembled Taylor-coefficient estimate for arbitrary square-integrable functions under the stated cumulant bound. It can be reused as the degree-$d\ge2$ input in the Poincaré reduction.
--
--   **Formalization Note**: The tensor norm and the $L^2$ norm are represented by real-valued expressions; `eLpNorm` takes values in $[0,\infty]$ and is converted with `toReal`. The statement is finite-dimensional and allows every $n\in\mathbb N$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_coordTensor_taylorTensor_sq_le_two_mul {d : ℕ} (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b)
--       (hcb : CumulantBound d b) {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
--       (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
--       (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f 2 (hV.law : Measure _)) :
--       ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
--         2 * b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/TaylorBound`](https://prove2.me/theorems/ef8651c6-ddf2-4f86-883a-e9e4c00f2d13).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342).
--
--   Selected supporting theorems: [`convexOn_of_hessian_ge`](https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d), [`norm_coordTensor_taylorTensor_inner_sq_le_of_basis`](https://prove2.me/theorems/f6507f16-38d4-4c99-9d45-dccf8890a2d6), [`taylorTensor_add`](https://prove2.me/theorems/2ed3b61d-3daf-4e91-b963-da93092fcaf2), [`cumulantBound_jointSpace`](https://prove2.me/theorems/88c575f1-15b2-4a92-828b-6fef20c27f09), [`exists_copies`](https://prove2.me/theorems/5967f3b2-764f-4fd4-8e97-8cae228211c5).
--
--   Previous: [`norm_coordTensor_taylorTensor_sq_le_of_smooth`](https://prove2.me/theorems/ad272b35-4fb6-4f10-b3ea-e0b98ec982a2).
--
--   [Source excerpt, lines 503–508](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/TaylorBound.lean#L503-L508) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Proposition 7.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 28.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/TaylorBound.lean#L502-L585 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.TaylorBound`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_two_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_TaylorBound

set_option autoImplicit false
open MeasureTheory FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.L2

theorem FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_two_mul_readable {d : ℕ} (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b)
    (hcb : CumulantBound d b) {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f 2 (hV.law : Measure _)) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
      2 * b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2 := by sorry
