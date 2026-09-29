-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_regularizer_perturbation_bound
-- name    : MatrixCompletion.NoSpuriousMin.regularizer_perturbation_bound
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-14T01:27:39.220159+00:00
-- url     : https://prove2.me/theorems/3eaa73c7-24fd-43f0-a7f9-e0fdf29af8f3
-- title:
--   Regularizer contribution to $K$: $\langle\Delta,\nabla^2 R(X)[\Delta]\rangle-4\langle\nabla R(X),\Delta\rangle \le 199.54\,\alpha^2\|\Delta\|_F^2-0.3\sum_i\|\Delta_i\|^4$
-- statement:
--   Setting for the Ge–Lee–Ma / Chen–Li matrix-completion objective $f(X)=\tfrac12\|P_\Omega(ZZ^\top-XX^\top)\|_F^2+\lambda R(X)$ with the row regularizer
--   $$R(X)=\sum_i\big(\|X_{i,\cdot}\|_2-\alpha\big)_+^4 .$$
--
--   Let $Z\in\mathbb R^{d\times r}$ be the ground-truth factor, let $U$ be any other factorization of the same matrix ($UU^\top=ZZ^\top$), and write $\Delta=X-U$ for the error direction. Assume the regularization radius is above the row-norm scale of $Z$, i.e. $\alpha\ge 100\,\|Z\|_{2\to\infty}$, where $\|Z\|_{2\to\infty}=\max_i\|Z_{i,\cdot}\|_2$.
--
--   Then the regularizer's contribution to the auxiliary function $K(X)=\langle\Delta,\nabla^2f(X)[\Delta]\rangle-4\langle\nabla f(X),\Delta\rangle$ obeys
--   $$\big\langle \Delta,\nabla^2R(X)[\Delta]\big\rangle-4\big\langle\nabla R(X),\Delta\big\rangle \;\le\; 199.54\,\alpha^2\|\Delta\|_F^2\;-\;0.3\sum_i\|\Delta_{i,\cdot}\|_2^4 .$$
--
--   This is Chen–Li's Lemma 4.10, a sharpened form of Lemma 11 of Ge–Jin–Zheng (2017): the point of the sharpening is the **negative quartic term** $-0.3\sum_i\|\Delta_{i,\cdot}\|_2^4$, which is what later absorbs the $19\|\Omega-pJ\|\sum_i\|\Delta_{i,\cdot}\|_2^4$ produced by the sampling estimate (Lemma 4.9) once $\lambda\ge 100\|\Omega-pJ\|$.
--
--   The proof is a per-row estimate. Rows with $\|X_{i,\cdot}\|<\alpha$ contribute nothing on the left because $(\|X_{i,\cdot}\|-\alpha)_+=0$. For a row with $\|X_{i,\cdot}\|\ge\alpha$, the hypothesis $\|U_{i,\cdot}\|=\|Z_{i,\cdot}\|\le\alpha/100$ gives $\langle X_{i,\cdot},\Delta_{i,\cdot}\rangle\ge 0.99\|X_{i,\cdot}\|^2$ and $0.99\|X_{i,\cdot}\|\le\|\Delta_{i,\cdot}\|\le 1.01\|X_{i,\cdot}\|$, whence the row's contribution is at most $12(\|X_{i,\cdot}\|-\alpha)_+^2\|\Delta_{i,\cdot}\|^2-15.68(\|X_{i,\cdot}\|-\alpha)_+^3\|X_{i,\cdot}\|$; the cubic negative term then dominates and yields the stated row bound $199.54\,\alpha^2\|\Delta_{i,\cdot}\|^2-0.3\|\Delta_{i,\cdot}\|^4$.
--
--   Here `regHessQF α X V` is the quadratic form $\langle V,\nabla^2R(X)[V]\rangle$, `regGrad α X` is $\nabla R(X)$, `innerM` is the trace inner product, `frobSq` is $\|\cdot\|_F^2$, `rowNorm A i` is $\|A_{i,\cdot}\|_2$ and `twoInftyNorm` is $\|\cdot\|_{2\to\infty}$.
-- source:
--   Ji Chen and Xiaodong Li, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142):1-39, 2019; arXiv:1711.01742v3, Lemma 4.10 and its proof in Appendix B (eqs. (B.1)-(B.6)). A modification of Lemma 11 of Rong Ge, Chi Jin, Yi Zheng, No Spurious Local Minima in Nonconvex Low Rank Problems, ICML 2017, arXiv:1704.00708.

import Definitions.Def_MCNoSpuriousMinModel
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.regularizer_perturbation_bound
    {d r : ℕ} (Z X U : Matrix (Fin d) (Fin r) ℝ) (α : ℝ) (hα : 0 < α)
    (hU : U * Uᵀ = Z * Zᵀ) (hα1 : 100 * twoInftyNorm Z ≤ α) :
    regHessQF α X (X - U) - 4 * innerM (regGrad α X) (X - U)
      ≤ 199.54 * α ^ 2 * frobSq (X - U) - 0.3 * ∑ i, rowNorm (X - U) i ^ 4 := by sorry
