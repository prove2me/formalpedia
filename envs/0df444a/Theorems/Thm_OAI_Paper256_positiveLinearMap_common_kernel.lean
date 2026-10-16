-- Prove2me | Theorems.Thm_OAI_Paper256_positiveLinearMap_common_kernel
-- name    : OAI.Paper256.positiveLinearMap_common_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:09:54.105136+00:00
-- url     : https://prove2.me/theorems/9c64ad08-481a-4bd6-b114-b8db8347240e
-- title:
--   For a positive linear map, the kernel at the identity is a common kernel
-- statement:
--   Write $\mathrm{Sym}_k$ for the real vector space of symmetric $k\times k$ real matrices. For a symmetric matrix $M$ write $M\succeq0$ if $M$ is positive semidefinite ($v^\top Mv\ge0$ for all real vectors $v$) and $M\succ0$ if it is positive definite ($v^\top Mv>0$ for all $v\neq0$). Let $D:\mathrm{Sym}_m\to\mathrm{Sym}_n$ be a *positive* linear map, i.e. $D(X)\succeq0$ whenever $X\succeq0$. If $v\in\mathbb{R}^n$ satisfies $D(I_m)v=0$, then
--   $$D(X)\,v=0\qquad\text{for every }X\in\mathrm{Sym}_m .$$
--   In other words, $\ker D(I_m)\subseteq\ker D(X)$ for all symmetric $X$.
--
--   This is what makes the compression of a spectrahedral representation possible: applied to the restriction of a pencil to one block of variables, it shows that the kernel of the matrix at the identity is shared by all matrices of that block, so those directions can be removed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PositiveMaps.lean#L30-L45

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology

open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem OAI.Paper256.positiveLinearMap_common_kernel {m n : ℕ} (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ X : Sym m, (X : Mat m ℝ).PosSemidef → (D X : Mat n ℝ).PosSemidef)
    (X : Sym m) (v : Fin n → ℝ) (hv : (D 1 : Mat n ℝ) *ᵥ v = 0) :
    (D X : Mat n ℝ) *ᵥ v = 0 := by sorry
