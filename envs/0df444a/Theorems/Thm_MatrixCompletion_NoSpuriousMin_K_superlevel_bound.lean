-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_K_superlevel_bound
-- name    : MatrixCompletion.NoSpuriousMin.K_superlevel_bound
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-08-04T14:12:45.680297+00:00
-- url     : https://prove2.me/theorems/cf4362a6-da2c-48d7-9d19-e52e16129c05
-- title:
--   Negative-definite quadratic bound on $K$: $K(X)\le p(-1.999a^2+6.001ab-6b^2)$ (Chen–Li eq. (4.14), exact case)
-- statement:
--   In the setting of the goal theorem, along every aligned direction $\Delta=X-U$ (with $UU^\top=ZZ^\top$, $X^\top U\succeq0$), writing $a=\|\Delta^\top\Delta\|_F$ and $b=\|\Delta^\top U\|_F$:
--
--   $$K(X)\ \le\ p\bigl(-1.999\,a^2+6.001\,ab-6\,b^2\bigr).$$
--
--   The quadratic form on the right is negative definite ($6.001^2<4\cdot1.999\cdot6$), so it is $\le 0$ with equality only at $a=b=0$. Combined with $K(\hat X)\ge 0$ at any local minimum, this forces $\Delta^\top\Delta=0$, i.e. $\hat X=U$ — the entire landscape argument in one inequality. The proof combines the decomposition of $K$, the perturbation bound, the expansion $\|XX^\top-UU^\top\|_F^2=\|\Delta\Delta^\top\|_F^2+2\|\Delta U^\top\|_F^2+2\langle\Delta U^\top,U\Delta^\top\rangle+4\langle\Delta\Delta^\top,U\Delta^\top\rangle$, and the trace inequalities $\langle\Delta U^\top,U\Delta^\top\rangle=\|\Delta^\top U\|_F^2$ and $\langle\Delta^\top\Delta,(U+\Delta)^\top U\rangle\ge0$ furnished by the alignment.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3) [THE canonical reference: all milestones follow its Section 4], p. 20, eq. (4.14), obtained via eqs. (4.8)-(4.13), exact-rank specialization (psi = 0). The psd trace identities (4.10)-(4.13) use the alignment X^T U >= 0 from Section 4.2.1.

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.LinearAlgebra.Matrix.PosDef
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.K_superlevel_bound
    {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (Z X U : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (p μ κ lam α : ℝ)
    (hμ : 1 ≤ μ) (hκ : 1 ≤ κ) (hcond : sigmaMax Z ≤ κ * sigmaMin Z)
    (hσ : 0 < sigmaMin Z)
    (hinc : Incoherent μ Z) (hZnorm : frobSq Z = (r : ℝ))
    (hα1 : 100 * twoInftyNorm Z ≤ α) (hα2 : α ≤ 200 * twoInftyNorm Z)
    (hlam1 : 100 * sampDevNorm Ω p ≤ lam) (hlam2 : lam ≤ 200 * sampDevNorm Ω p)
    (hp : SampleCondition d r p μ κ)
    (hgood : GoodSample Z Ω p)
    (hU : U * Uᵀ = Z * Zᵀ) (hpsd : (Xᵀ * U).PosSemidef) :
    Kfun Z Ω lam α X U ≤
      p * (-(1999 / 1000) * frobSq ((X - U)ᵀ * (X - U))
        + (6001 / 1000) * frobNorm ((X - U)ᵀ * (X - U)) * frobNorm ((X - U)ᵀ * U)
        - 6 * frobSq ((X - U)ᵀ * U)) := by sorry
