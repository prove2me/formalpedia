-- Prove2me | Theorems.Thm_ModularForm_mdifferentiable_heckeU
-- name    : ModularForm.mdifferentiable_heckeU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/f99d76db-114b-59c2-856b-577cdfd4ee73
-- title:
--   Holomorphy of Uₚ f on the upper half-plane
-- statement:
--   Let $f : \mathbb{H} \to \mathbb{C}$ be a function on the upper half-plane which is differentiable in the sense of the manifold structure on $\mathbb{H}$ and on $\mathbb{C}$ given by the trivial model with corners of $\mathbb{C}$ over itself, i.e. holomorphic on $\mathbb{H}$. Let $k$ be an integer and $p$ a natural number. The assertion is that the function $\mathrm{heckeU}\ k\ p\ f$, namely the finite sum
--   $$\sum_{j=0}^{p-1} f \mid_{k} M_{p,j},$$
--   where $\mid_{k}$ denotes the weight-$k$ slash action of $\mathrm{GL}_2(\mathbb{R})$ and $M_{p,j} \in \mathrm{GL}_2(\mathbb{R})$ is the upper triangular matrix with diagonal entries $1, p$ and upper right entry $j$ (with the convention that $M_{0,j}$ is the identity, a case in which the sum is empty in any event), is again differentiable for the same model with corners on source and target, i.e. holomorphic on $\mathbb{H}$.
--
--   This records that the operator $U_p$, formed from the slash action of the matrices $\begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}$ for $0 \le j < p$, preserves holomorphy on the upper half-plane; it is the analytic half of the construction of $U_p$ as an operator on modular and cusp forms. It is used throughout the study of $U_p$-eigenforms, in particular in the level-lowering and degeneracy-map computations relating $U_p$-eigenvalues to $q$-expansion coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_mdifferentiable_heckeU.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.mdifferentiable_heckeU {f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k p f) := by sorry
