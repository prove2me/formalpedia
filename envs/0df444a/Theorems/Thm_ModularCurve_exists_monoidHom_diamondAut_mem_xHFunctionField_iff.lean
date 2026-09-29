-- Prove2me | Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_xHFunctionField_iff
-- name    : ModularCurve.exists_monoidHom_diamondAut_mem_xHFunctionField_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/94ca3cfb-b2df-5571-920c-3cfa5437c01c
-- title:
--   X_H function field as diamond-fixed subfield of X₁
-- statement:
--   Let $M$ be a nonzero natural number and $H$ a subgroup of $(\mathbb{Z}/M)^\times$. Write $F_1 =$ [`ModularCurve.x1FunctionField M`](def/ModularCurve_X1.html#L137) for the intermediate field `qExpFunctionFieldC ℚ (Gamma1 M)` of the Laurent series field $\mathbb{Q}((q))$ attached to $\Gamma_1(M)$, and $F_H =$ [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79) for the analogous intermediate field `qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)`. The hypothesis is that for every natural number $d$ coprime to $M$ there is a $\mathbb{Q}$-algebra automorphism $\sigma$ of $F_1$ satisfying `IsDiamondAut M d σ`, i.e. $d$ is coprime to $M$ and, for all weights $k$, all modular forms $f,g$ of weight $k$ on $\Gamma_1(M)$ (viewed in $GL_2(\mathbb{R})$) with integral $q$-expansions $p_f,p_g \in \mathbb{Z}[[q]]$ (their images in $\mathbb{C}[[q]]$ being the $q$-expansions of $f$ and $g$) and $p_g$ giving a nonzero Laurent series over $\mathbb{Q}$, and for every $\gamma \in \Gamma_0(M) \subseteq SL_2(\mathbb{Z})$ whose upper-left entry reduces to $d$ in $\mathbb{Z}/M$, the coefficientwise image in $\mathbb{C}((q))$ of $\sigma(p_f/p_g)$ times the $q$-expansion of $g\mid_k\gamma$ equals the $q$-expansion of $f\mid_k\gamma$. The conclusion asserts the existence of a monoid homomorphism $\delta$ from $H$ to the group of $\mathbb{Q}$-algebra automorphisms of $F_1$ such that $\delta(u) =$ [`ModularCurve.diamondAut M`](def/ModularCurve_X1Diamond.html#L66) applied to the least nonnegative residue representing $u$, and such that for every $x \in F_1$ one has $x \in F_H$ if and only if $\delta(u)\,x = x$ for all $u \in H$.
--
--   This is the function-field form of the statement that $X_1(M) \to X_H(M)$ is a Galois covering whose deck transformations are the diamond operators $\langle d\rangle$ with $d \in H$: the subfield cut out by $\Gamma_H(M)$ is exactly the fixed field of the image of $H$. It is used downstream in the treatment of the diamond automorphisms (their multiplicativity and their reductions) and in the construction of pull-back and push-forward maps between the Jacobians of $X_1(M)$ and $X_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_monoidHom_diamondAut_mem_xHFunctionField_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_monoidHom_diamondAut_mem_xHFunctionField_iff
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hdia : ∀ d : ℕ, Nat.Coprime d M →
      ∃ σ : ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M,
        ModularCurve.IsDiamondAut M d σ) :
    ∃ δ : H →* (ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M),
      (∀ u : H, δ u = ModularCurve.diamondAut M (((u : (ZMod M)ˣ) : ZMod M).val)) ∧
      ∀ x : ModularCurve.x1FunctionField M,
        (x : LaurentSeries ℚ) ∈ ModularCurve.xHFunctionField M H ↔ ∀ u : H, δ u x = x := by sorry
