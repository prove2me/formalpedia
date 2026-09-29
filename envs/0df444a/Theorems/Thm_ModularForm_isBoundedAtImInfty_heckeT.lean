-- Prove2me | Theorems.Thm_ModularForm_isBoundedAtImInfty_heckeT
-- name    : ModularForm.isBoundedAtImInfty_heckeT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/8d04f3f6-88fa-5055-b10d-e1d6631bbd39
-- title:
--   Boundedness at i∞ is preserved by Tₚ
-- statement:
--   Let $f:\mathbb{H}\to\mathbb{C}$ be a function on the upper half-plane which is bounded at infinity, i.e. `UpperHalfPlane.IsBoundedAtImInfty f`: $f$ is bounded along the filter of points with large imaginary part. Let $k\in\mathbb{Z}$ be a weight and $p$ a natural number, with no primality, positivity or modularity assumption on $p$, $k$ or $f$. The assertion is that [`ModularForm.heckeT k p f`](def/ModularForm_HeckeOperator.html#L96) is again bounded at infinity. Here `heckeT k p f` is, by definition, the sum of `heckeU k p f`, namely $\sum_{j<p} f\mid[k]\,$`heckeMatrix p j` where the slash is the weight-$k$ action of $\mathrm{GL}_2(\mathbb{R})$ on functions on $\mathbb{H}$ and `heckeMatrix p j` is the $j$-th of the $p$ matrices used in the definition of the Hecke operator, and the single extra term $f\mid[k]\,$`heckeDiagMatrix p`, where `heckeDiagMatrix p` is the identity if $p=0$ and otherwise the element `upperTriangularGL p 0 1` of $\mathrm{GL}_2(\mathbb{R})$, the upper-triangular matrix with diagonal entries $p$ and $1$ and upper-right entry $0$. Thus for $p\neq 0$ the conclusion concerns $\tau\mapsto p^{-1}\sum_{j<p} f((\tau+j)/p)+p^{k-1}f(p\tau)$ up to the normalisation built into the slash action, and for $p=0$ it concerns $f$ itself.
--
--   This is the growth half of the statement that the Hecke operator $T_p$ preserves modular and cusp forms: each of the $p+1$ matrices involved is upper triangular, so that translating $f$ by it preserves boundedness as $\operatorname{Im}\tau\to\infty$. It is used in the construction of $T_p$ on spaces of modular and cusp forms and in the computations relating $q$-expansion coefficients of an eigenform to its eigenvalue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_isBoundedAtImInfty_heckeT.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.isBoundedAtImInfty_heckeT {f : UpperHalfPlane → ℂ} (hf : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) (p : ℕ) : UpperHalfPlane.IsBoundedAtImInfty (ModularForm.heckeT k p f) := by sorry
