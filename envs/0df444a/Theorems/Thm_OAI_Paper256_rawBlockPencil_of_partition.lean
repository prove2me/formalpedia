-- Prove2me | Theorems.Thm_OAI_Paper256_rawBlockPencil_of_partition
-- name    : OAI.Paper256.rawBlockPencil_of_partition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:13:23.255874+00:00
-- url     : https://prove2.me/theorems/547f3a37-329f-4a35-ba12-58529bf78a85
-- title:
--   Assembling a raw block pencil from an index partition adapted to the first partial map
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
--   **Theorem.** Let $K\subseteq\mathcal A$, let $L:\mathcal A\to\mathrm{Sym}_m$ be linear, let $a,c\ge1$, and let $\pi:\{1,\dots,a\}\sqcup\{1,\dots,c\}\to\{1,\dots,m\}$ be a bijection with restrictions $f(i)=\pi(i)$ on the first part and $g(j)=\pi(j)$ on the second part. For an $m\times m$ matrix $N$ write $N_{f,f}=(N_{f(i)f(i')})$, $N_{f,g}=(N_{f(i)g(j)})$ and $N_{g,g}=(N_{g(j)g(j')})$. Assume
--
--   - $K=\{x\in\mathcal A: L(x)\succeq0\}$;
--   - $L_1$ and $L_2$ are positive maps;
--   - for every $X\in\mathrm{Sym}_4$ the rows of $L_1(X)$ indexed by the second part vanish: $L_1(X)_{g(j),k}=0$ for all $j$ and all $k\in\{1,\dots,m\}$;
--   - $L_1(I_4)_{f,f}\succ0$ and $L_2(I_4)_{g,g}\succ0$.
--
--   Then
--   $$K\ \text{admits a raw block pencil.}$$
--
--   Reordering the coordinates of a representing pencil along a partition adapted to $L_1$ turns the representation into the $2\times2$ block form above, in which $X$ enters only the upper-left block. This is the assembly step that follows the spectral splitting of $L_1(I_4)$.
--
--   **Formalization Note** The raw block pencil is the structure `RawBlockPencil K`, and the conclusion is its nonemptiness. The bijection is an equivalence `e : Fin a ⊕ Fin c ≃ Fin m` with $f$ and $g$ the compositions with `Sum.inl` and `Sum.inr`; $L_1,L_2,L_3$ are `pencilFirst L`, `pencilSecond L` and `pencilParameter L`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/SplitAssembly.lean#L51-L88

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

open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator

theorem OAI.Paper256.rawBlockPencil_of_partition {m a c : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym m) (ha : 0 < a) (hc : 0 < c)
    (e : (Fin a ⊕ Fin c) ≃ Fin m)
    (hrep : K = {x | (L x : Mat m ℝ).PosSemidef})
    (hfirst : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef →
      (pencilFirst L X : Mat m ℝ).PosSemidef)
    (hsecond : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef →
      (pencilSecond L X : Mat m ℝ).PosSemidef)
    (hrow : ∀ (X : Sym 4) (i : Fin c) (j : Fin m),
      (pencilFirst L X : Mat m ℝ) (e (Sum.inr i)) j = 0)
    (hD : ((pencilFirst L 1 : Mat m ℝ).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)).PosDef)
    (hE : ((pencilSecond L 1 : Mat m ℝ).submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)).PosDef) :
    Nonempty (RawBlockPencil K) := by sorry
