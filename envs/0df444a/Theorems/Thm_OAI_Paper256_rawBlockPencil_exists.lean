-- Prove2me | Theorems.Thm_OAI_Paper256_rawBlockPencil_exists
-- name    : OAI.Paper256.rawBlockPencil_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:15:51.496116+00:00
-- url     : https://prove2.me/theorems/963136ce-caa9-4903-8d90-114fc5f3011c
-- title:
--   A spectrahedral representation that is positive definite at the base point yields a raw block pencil
-- statement:
--   Write $\mathrm{Sym}_k$ for the real vector space of symmetric $k\times k$ real matrices. For a symmetric matrix $M$ write $M\succeq0$ if $M$ is positive semidefinite ($v^\top Mv\ge0$ for all real vectors $v$) and $M\succ0$ if it is positive definite ($v^\top Mv>0$ for all $v\neq0$). Let $\mathcal A=\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$, with points written $(X,Z,y)$. For a linear map $L:\mathcal A\to\mathrm{Sym}_m$ write its three partial maps
--   $$L_1(X)=L(X,0,0),\qquad L_2(Z)=L(0,Z,0),\qquad L_3(y)=L(0,0,y),$$
--   so that $L(X,Z,y)=L_1(X)+L_2(Z)+L_3(y)$. A linear map between spaces of symmetric matrices is called *positive* if it sends positive semidefinite matrices to positive semidefinite matrices.
--
--   A *raw block pencil* for $K$ consists of integers $a,c\ge1$ and linear maps
--   $$D,F:\mathrm{Sym}_4\to\mathrm{Sym}_a,\quad E:\mathrm{Sym}_4\to\mathrm{Sym}_c,\quad C:\mathrm{Sym}_4\to\mathbb{R}^{a\times c},\quad A:\mathbb{R}^3\to\mathrm{Sym}_a,\quad B:\mathbb{R}^3\to\mathbb{R}^{a\times c},\quad G:\mathbb{R}^3\to\mathrm{Sym}_c$$
--   such that $D$ and $E$ are positive, $D(I_4)\succ0$, $E(I_4)\succ0$, and for all $(X,Z,y)\in\mathcal A$
--   $$(X,Z,y)\in K\iff\begin{pmatrix}D(X)+F(Z)+A(y)&C(Z)+B(y)\\ (C(Z)+B(y))^\top&E(Z)+G(y)\end{pmatrix}\succeq0 .$$
--
--   **Theorem.** Let $K\subseteq\mathcal A$ and let $L:\mathcal A\to\mathrm{Sym}_m$ be linear with $L(I_4,I_4,0)\succ0$. Assume that $L$ represents $K$, i.e. $K=\{x\in\mathcal A:L(x)\succeq0\}$, and that the slice of $K$ at $y=0$ is a product of positive semidefinite cones: for all $X,Z\in\mathrm{Sym}_4$, $(X,Z,0)\in K$ if and only if $X\succeq0$ and $Z\succeq0$. Then
--   $$K\ \text{admits a raw block pencil.}$$
--
--   The point $(I_4,I_4,0)$ is the base point of the hyperbolicity cone in $\mathcal A$, and the hypotheses are what a compressed spectrahedral representation of that cone would satisfy. The theorem converts such a representation into block form, the starting point for normalizing the diagonal blocks to identities and eventually reaching a contradiction.
--
--   **Formalization Note** The representing map is called `C` in Lean and the base point is `basePoint = ((1, 1), 0)`. The raw block pencil is the structure `RawBlockPencil K`, and the conclusion is its nonemptiness; $L_1,L_2,L_3$ are `pencilFirst`, `pencilSecond` and `pencilParameter`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilSplit.lean#L13-L65

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
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization

open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator

theorem OAI.Paper256.rawBlockPencil_exists {m : ℕ} (K : Set Ambient)
    (C : Ambient →ₗ[ℝ] Sym m) (hC : (C basePoint : Mat m ℝ).PosDef)
    (hrep : K = {x | (C x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    Nonempty (RawBlockPencil K) := by sorry
