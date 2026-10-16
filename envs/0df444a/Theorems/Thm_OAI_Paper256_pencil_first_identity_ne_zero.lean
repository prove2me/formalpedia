-- Prove2me | Theorems.Thm_OAI_Paper256_pencil_first_identity_ne_zero
-- name    : OAI.Paper256.pencil_first_identity_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:10:23.180771+00:00
-- url     : https://prove2.me/theorems/5c6cac1a-9738-4e78-ab7f-b31191f4ff2d
-- title:
--   In a spectrahedral representation with product zero slice, the first partial map is nonzero at the identity
-- statement:
--   Write $\mathrm{Sym}_k$ for the real vector space of symmetric $k\times k$ real matrices. For a symmetric matrix $M$ write $M\succeq0$ if $M$ is positive semidefinite ($v^\top Mv\ge0$ for all real vectors $v$) and $M\succ0$ if it is positive definite ($v^\top Mv>0$ for all $v\neq0$). Let $\mathcal A=\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$, with points written $(X,Z,y)$. For a linear map $L:\mathcal A\to\mathrm{Sym}_m$ write its three partial maps
--   $$L_1(X)=L(X,0,0),\qquad L_2(Z)=L(0,Z,0),\qquad L_3(y)=L(0,0,y),$$
--   so that $L(X,Z,y)=L_1(X)+L_2(Z)+L_3(y)$. A linear map between spaces of symmetric matrices is called *positive* if it sends positive semidefinite matrices to positive semidefinite matrices.
--
--   Let $K\subseteq\mathcal A$ and let $L:\mathcal A\to\mathrm{Sym}_m$ be linear. Assume that (i) $L$ represents $K$, i.e. $K=\{x\in\mathcal A:L(x)\succeq0\}$, and (ii) the slice of $K$ at $y=0$ is a product of positive semidefinite cones: for all $X,Z\in\mathrm{Sym}_4$, $(X,Z,0)\in K$ if and only if $X\succeq0$ and $Z\succeq0$. Then
--   $$L_1(I_4)\neq0 .$$
--
--   In the argument that the hyperbolicity cone in $\mathcal A$ studied here is not a spectrahedron, one assumes such a representation and analyses the positive semidefinite matrix $L_1(I_4)$. Together with the companion result that $L_1(I_4)$ is not positive definite, this shows that $L_1(I_4)$ has both positive and zero eigenvalues, which is needed to split the pencil into two nontrivial blocks.
--
--   **Formalization Note** Points of $\mathcal A$ (the type `Ambient`) are pairs `((X, Z), y)`, and $L_1,L_2,L_3$ are `pencilFirst L`, `pencilSecond L` and `pencilParameter L`. The conclusion compares the underlying $m\times m$ matrix with $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/SplitBasic.lean#L50-L66

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
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic

open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator

theorem OAI.Paper256.pencil_first_identity_ne_zero {m : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym m) (hrep : K = {x | (L x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    (pencilFirst L 1 : Mat m ℝ) ≠ 0 := by sorry
