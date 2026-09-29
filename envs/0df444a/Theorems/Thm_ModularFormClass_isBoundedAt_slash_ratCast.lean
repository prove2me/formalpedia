-- Prove2me | Theorems.Thm_ModularFormClass_isBoundedAt_slash_ratCast
-- name    : ModularFormClass.isBoundedAt_slash_ratCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/70548295-3516-5fa6-9e57-c7fb9d2fedbe
-- title:
--   Slashing a modular form by a rational matrix preserves cusp boundedness
-- statement:
--   Let $F$ be a type of functions on the upper half-plane $\mathbb{H}$ with values in $\mathbb{C}$ (a `FunLike` structure), let $\Gamma$ be an arithmetic subgroup of $\mathrm{GL}_2(\mathbb{R})$ (Mathlib's `Subgroup.IsArithmetic`), let $k$ be an integer, and assume $F$ is a class of modular forms of weight $k$ on $\Gamma$, i.e. each element is holomorphic, weight-$k$ invariant under $\Gamma$ and bounded at all cusps of $\Gamma$. Given $f : F$, a matrix $g \in \mathrm{GL}_2(\mathbb{Q})$, and a point $c$ of the one-point compactification $\mathbb{P}^1(\mathbb{R}) =$ `OnePoint ℝ` which is a cusp of $\Gamma$ in the sense of `IsCusp`, the conclusion is `OnePoint.IsBoundedAt c` applied to the weight-$k$ slash $f \mid_k \iota(g)$ and to $k$, where $\iota(g) \in \mathrm{GL}_2(\mathbb{R})$ is the image of $g$ under the entrywise map induced by the ring homomorphism $\mathbb{Q} \to \mathbb{R}$. That is, the slashed function $f \mid_k \iota(g)$ is bounded at the cusp $c$ in Mathlib's sense: for every real matrix carrying $\infty$ to $c$, the further slash of $f \mid_k \iota(g)$ by it is bounded along the filter at $i\infty$.
--
--   This is the standard fact that the weight-$k$ translate of a modular form by a rational matrix still satisfies the boundedness condition at every cusp, the growth half of the statement that $f \mid_k g$ is a modular form for a commensurable group. It supplies the cusp conditions needed for the Hecke operators $U_p$ and $T_p$, which are finite sums of such slashes by upper triangular rational matrices, and is used downstream in the study of mod $p$ modular forms ([`ModPForms.heckeV_mem_modPMod_mul`](thm.html#ModPForms.heckeV_mem_modPMod_mul)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularFormClass_isBoundedAt_slash_ratCast.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularFormClass.isBoundedAt_slash_ratCast {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [ModularFormClass F Γ k] (f : F) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : OnePoint.IsBoundedAt c (SlashAction.map k (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g) ⇑f) k := by sorry
