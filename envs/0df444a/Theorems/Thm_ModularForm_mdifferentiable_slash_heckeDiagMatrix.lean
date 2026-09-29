-- Prove2me | Theorems.Thm_ModularForm_mdifferentiable_slash_heckeDiagMatrix
-- name    : ModularForm.mdifferentiable_slash_heckeDiagMatrix
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/2e8ec639-789e-5ab0-bbdb-55be1ca38447
-- title:
--   Holomorphy is preserved by slashing with diag(d,1)
-- statement:
--   Fix a natural number $d$ and an integer $k$, and let $f : \mathbb{H} \to \mathbb{C}$ be a function on the upper half-plane which is $\mathcal{M}$-differentiable for the model with corners given by $\mathbb{C}$ over itself, i.e. holomorphic in the sense of complex manifolds. Let [`ModularForm.heckeDiagMatrix d`](def/ModularForm_HeckeOperator.html#L21) be the element of $\mathrm{GL}_2(\mathbb{R})$ which is the identity when $d = 0$ and otherwise the upper triangular matrix $\begin{pmatrix} d & 0 \\ 0 & 1\end{pmatrix}$, viewed as invertible because its determinant $d \cdot 1$ is nonzero. The conclusion is that the image of $f$ under the weight-$k$ slash action of this matrix, $f \mid_k \mathrm{diag}(d,1)$, is again holomorphic in the same sense, i.e. $\mathcal{M}$-differentiable for the model with corners of $\mathbb{C}$ over itself. No growth, periodicity or equivariance condition on $f$ is assumed: the statement concerns the holomorphy clause alone, for an arbitrary holomorphic function on $\mathbb{H}$.
--
--   This is the holomorphy clause for the degeneracy (rescaling) map $f \mapsto f \mid_k \mathrm{diag}(d,1)$ on modular forms, which raises the level by a factor dividing $d$ and is one ingredient of the Hecke operator $T_d$ (or $U_d$) on forms. It is used in establishing that the rescaled form lies in the relevant space of mod $p$ forms, via [`ModPForms.heckeV_mem_modPMod_mul`](thm.html#ModPForms.heckeV_mem_modPMod_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_mdifferentiable_slash_heckeDiagMatrix.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ModularForm

theorem ModularForm.mdifferentiable_slash_heckeDiagMatrix (d : ℕ) (k : ℤ)
    {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (SlashAction.map k (ModularForm.heckeDiagMatrix d) f) := by sorry
