-- Prove2me | Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_Schur_differential_scalar
-- name    : OAI.PermanentBorder.PolarAnalysis.Schur.differential_scalar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:39:07.18899+00:00
-- url     : https://prove2.me/theorems/1fbac707-2fdf-449b-a5e7-fa5e7ee195eb
-- title:
--   Derivative of a Schur complement as a pairing with the left and right kernel vectors
-- statement:
--   Let $V$ be a complex normed space, $\iota$ a finite index set and $x\in V$. Let $a:V\to\mathbb{C}$, $\beta,\gamma:V\to\mathbb{C}^{\iota}$ and $E:V\to\mathbb{C}^{\iota\times\iota}$ be maps such that $a$ and all coordinate functions $y\mapsto\beta(y)_i$, $y\mapsto\gamma(y)_i$, $y\mapsto E(y)_{ij}$ are complex differentiable at $x$, and assume $\det E(x)\neq0$. Consider the bordered matrices and the Schur complement
--   $$M(y)=\begin{pmatrix}a(y)&\beta(y)^{\top}\\ \gamma(y)&E(y)\end{pmatrix},\qquad s(y)=a(y)-\beta(y)^{\top}E(y)^{-1}\gamma(y),$$
--   and the normalised left and right kernel vectors at $x$,
--   $$\hat\lambda=\big(1,\,-\beta(x)^{\top}E(x)^{-1}\big),\qquad\hat\rho=\big(1,\,-E(x)^{-1}\gamma(x)\big)^{\top}.$$
--   Then for every direction $h\in V$
--
--   $$
--   Ds(x)[h]=\hat\lambda\,\big(DM(x)[h]\big)\,\hat\rho ,
--   $$
--
--   where $DM(x)[h]$ is the matrix $\big(DM_{pq}(x)[h]\big)_{p,q}$ of directional derivatives of the entries of $M$.
--
--   Since $\det M=\det E\cdot s$, the zeros of $s$ near $x$ are those of $\det M$. The formula expresses the directional derivatives of $s$ as the bilinear quantity $w^{\top}(\partial_hM)\,u$ evaluated at the kernel vectors $u=\hat\rho$ and $w^{\top}=\hat\lambda$; this is how conditions on derivatives of a determinant turn into bilinear polynomial equations in kernel vectors.
--
--   **Formalization Note** In Lean $s(y)$ is `scalar (a y) (β y) (γ y) (E y)` (with Mathlib's total matrix inverse), $M(y)$ is `block (a y) (β y) (γ y) (E y)`, the two vectors are `normalized (left (β x) (E x))` and `normalized (right (γ x) (E x))`, and $Ds(x)[h]$ is `fderiv ℂ s x h`. Under the hypotheses $s$ is differentiable at $x$, since $E(y)$ stays invertible near $x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SchurDifferentials.lean#L65-L117

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials

open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis OAI.PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem OAI.PermanentBorder.PolarAnalysis.Schur.differential_scalar {a : V → ℂ} {β γ : V → ι → ℂ}
    {E : V → Matrix ι ι ℂ} {x : V}
    (ha : DifferentiableAt ℂ a x)
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (h : V) :
    fderiv ℂ (fun y => scalar (a y) (β y) (γ y) (E y)) x h =
      normalized (left (β x) (E x)) ⬝ᵥ
        ((Matrix.of fun i j => fderiv ℂ (fun y => block (a y) (β y) (γ y) (E y) i j) x h)
          *ᵥ normalized (right (γ x) (E x))) := by sorry
