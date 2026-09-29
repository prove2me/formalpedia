-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/84e2cefb-edb3-59f9-9da3-4122ecdc68a6
-- title:
--   Whittaker functions: torus conjugation of the (1,2) unipotent
-- statement:
--   Let $v$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, let $\psi_v$ be an additive character of the completion $\mathbb{Q}_v :=$ `v.adicCompletion ℚ` with values in $\mathbb{C}$, and let $W$ be a complex-valued function on `LocalGL3 v`, the group $\mathrm{GL}_3(\mathbb{Q}_v)$ of invertible $3\times 3$ matrices over $\mathbb{Q}_v$. Assume `IsGL3PsiWhittakerFn ψv W`, i.e. for all $x,y,z \in \mathbb{Q}_v$ and all $g \in \mathrm{GL}_3(\mathbb{Q}_v)$ one has $W(u(x,y,z)\,g) = \psi_v(x+y)\,W(g)$, where $u(x,y,z)$ denotes the upper triangular unipotent matrix `upperUnipotent3 x y z` with entries $x$, $y$, $z$ in positions $(1,2)$, $(2,3)$, $(1,3)$. Then for every unit $a$ of $\mathbb{Q}_v$, every $x \in \mathbb{Q}_v$ and every $g \in \mathrm{GL}_3(\mathbb{Q}_v)$,
--   $$W\bigl(\iota(\mathrm{diag}(a,1))\,\bigl(u(x,0,0)\,g\bigr)\bigr) = \psi_v(a x)\,W\bigl(\iota(\mathrm{diag}(a,1))\,g\bigr),$$
--   where $\iota =$ `iotaGL` is the block embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$, $h \mapsto \mathrm{diag}(h,1)$, so that $\iota(\mathrm{diag}(a,1))$ is the diagonal matrix $\mathrm{diag}(a,1,1)$.
--
--   This is the elementary equivariance underlying the Fourier-theoretic behaviour of the torus line $a \mapsto W(\mathrm{diag}(a,1,1)g)$ of a $\psi_v$-Whittaker function on $\mathrm{GL}_3$: right translation of that line by the $(1,2)$-unipotent $u(x,0,0)$ multiplies it by $\psi_v(ax)$. It is used in the proof of convergence and non-vanishing of the local $\mathrm{GL}_3 \times \mathrm{GL}_1$ zeta integrals within the cubic-induction part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) (g : LocalGL3 v) :
    W (iotaGL (diagUnitGL2 a) * (upperUnipotent3 x 0 0 * g)) = ψv ((a : v.adicCompletion ℚ) * x) * W (iotaGL (diagUnitGL2 a) * g) := by sorry
