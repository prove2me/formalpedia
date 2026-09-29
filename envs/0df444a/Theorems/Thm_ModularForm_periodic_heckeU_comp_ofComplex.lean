-- Prove2me | Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex
-- name    : ModularForm.periodic_heckeU_comp_ofComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/5711f1c3-c1eb-5781-a87e-76c555cbbcc3
-- title:
--   Uₚ preserves 1-periodicity
-- statement:
--   Let $f : \mathbb{H} \to \mathbb{C}$ be any function on the upper half plane, $k$ an integer and $p$ a natural number. Write $g \mapsto g \circ$ `UpperHalfPlane.ofComplex` for precomposition with the retraction $\mathbb{C} \to \mathbb{H}$ which is the identity on points of positive imaginary part and takes a fixed value elsewhere, so that $f \circ$ `ofComplex` is a function $\mathbb{C} \to \mathbb{C}$. The hypothesis is that $f \circ$ `ofComplex` is periodic with period $1$, i.e. $f(\mathrm{ofComplex}(z+1)) = f(\mathrm{ofComplex}(z))$ for all $z \in \mathbb{C}$. The conclusion is that [`ModularForm.heckeU k p f`](def/ModularForm_HeckeOperator.html#L93) $\circ$ `ofComplex` is again periodic with period $1$. Here [`ModularForm.heckeU k p f`](def/ModularForm_HeckeOperator.html#L93) is the finite sum $\sum_{j < p} f \mid[k] \,$ `heckeMatrix p j` of weight-$k$ slash transforms, where `heckeMatrix p j` is the identity of $\mathrm{GL}_2(\mathbb{R})$ when $p = 0$ and otherwise the upper triangular matrix with rows $(1, j)$ and $(0, p)$; thus for $p \ge 1$ the value at $\tau$ is, up to the determinant and cocycle factors built into the slash action, $\sum_{j=0}^{p-1} f((\tau+j)/p)$, and for $p = 0$ the sum is empty. No modularity or holomorphy of $f$ is assumed.
--
--   This is the elementary stability statement that the Hecke operator $U_p$, defined by the matrices $\begin{pmatrix}1&j\\0&p\end{pmatrix}$, sends $1$-periodic functions to $1$-periodic functions, the shift $j \mapsto j+1$ permuting the summands modulo $p$. It is what allows $U_p f$ to be given a $q$-expansion, and it is used throughout the analysis of eigenforms and their $q$-expansion coefficients in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_periodic_heckeU_comp_ofComplex.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.periodic_heckeU_comp_ofComplex {f : UpperHalfPlane → ℂ} (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (k : ℤ) (p : ℕ) : Function.Periodic (ModularForm.heckeU k p f ∘ UpperHalfPlane.ofComplex) 1 := by sorry
