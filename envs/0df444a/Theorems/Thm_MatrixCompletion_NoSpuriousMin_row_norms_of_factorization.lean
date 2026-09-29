-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_row_norms_of_factorization
-- name    : MatrixCompletion.NoSpuriousMin.row_norms_of_factorization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T14:11:53.955978+00:00
-- url     : https://prove2.me/theorems/0af74686-5f57-4b38-ad6d-014424015e63
-- title:
--   Row norms are invariant across factorizations $UU^\top=ZZ^\top$ (Claim C.2)
-- statement:
--   If $U,Z\in\mathbb{R}^{d\times r}$ satisfy $UU^\top=ZZ^\top$, then every row satisfies $\|U_i\|=\|Z_i\|$; consequently $\|U\|_F=\|Z\|_F$. In particular all exact factors of $M=ZZ^\top$ are equally incoherent — the symmetric-case substitute for the row-norm bounds on both factors in the asymmetric analysis of Sun–Luo. (Immediate from $\|U_i\|^2=(UU^\top)_{ii}$.)
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3) [THE canonical reference: all milestones follow its Section 4], Section 4.3 (auxiliary fact used to transfer incoherence to the aligned factor U; immediate from ||U_i||^2 = (UU^T)_ii). Explicitly stated as Ge, Lee, Ma 2016, Matrix Completion has No Spurious Local Minimum, https://arxiv.org/abs/1605.07272 (v4), p. 21, Claim C.2.

import Definitions.Def_MCNoSpuriousMinModel
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.row_norms_of_factorization
    {d r : ℕ} (U Z : Matrix (Fin d) (Fin r) ℝ)
    (hU : U * Uᵀ = Z * Zᵀ) (i : Fin d) :
    rowNorm U i = rowNorm Z i := by sorry
