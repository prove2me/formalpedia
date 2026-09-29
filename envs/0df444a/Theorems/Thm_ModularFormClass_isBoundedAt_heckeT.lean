-- Prove2me | Theorems.Thm_ModularFormClass_isBoundedAt_heckeT
-- name    : ModularFormClass.isBoundedAt_heckeT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/25cbeda5-8d19-592d-8416-c64dd14fde75
-- title:
--   Tₚ f is bounded at every cusp
-- statement:
--   Let $F$ be a type whose elements are coerced to functions $\mathbb{H} \to \mathbb{C}$ on the upper half-plane, let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ that is arithmetic, let $k$ be an integer, and suppose $F$ is a class of weight-$k$ modular forms for $\Gamma$ (so each $f : F$ is holomorphic, satisfies the weight-$k$ transformation law under $\Gamma$, and is bounded at the cusps of $\Gamma$). Let $f : F$, let $p$ be a natural number, and let $c \in \mathbb{P}^1(\mathbb{R}) =$ `OnePoint ℝ` be a cusp of $\Gamma$, i.e. `IsCusp c Γ` holds. The conclusion is that the function $$\mathrm{heckeT}\,k\,p\,f \;=\; \sum_{j = 0}^{p-1} f \mid_k \begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix} \;+\; f \mid_k \begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$$ is bounded at $c$ in weight $k$, in the sense of `OnePoint.IsBoundedAt`: its weight-$k$ slashes by matrices carrying $\infty$ to $c$ are bounded towards $i\infty$. No condition relating $p$ to a level is imposed, and $p = 0$ is allowed: by convention both Hecke matrices are then the identity, so the sum is empty and the second term is $f \mid_k 1$.
--
--   This is the boundedness-at-the-cusps half of the statement that the Hecke operator $T_p$ preserves modular forms; together with the corresponding holomorphy and weight-$k$ invariance statements it supplies the `bdd_at_cusps` datum needed to package $T_p f$ as a modular form on $\Gamma_0(N)$. The companion result for cusp forms replaces boundedness by vanishing at the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularFormClass_isBoundedAt_heckeT.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularFormClass.isBoundedAt_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : OnePoint.IsBoundedAt c (ModularForm.heckeT k p ⇑f) k := by sorry
