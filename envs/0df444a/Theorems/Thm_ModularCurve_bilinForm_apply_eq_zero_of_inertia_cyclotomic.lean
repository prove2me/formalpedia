-- Prove2me | Theorems.Thm_ModularCurve_bilinForm_apply_eq_zero_of_inertia_cyclotomic
-- name    : ModularCurve.bilinForm_apply_eq_zero_of_inertia_cyclotomic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/598811ec-abd0-5ac1-8d0c-36d0f14c2099
-- title:
--   Inertia-cyclotomic vectors are isotropic for a twisted pairing
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $M$ be a nonzero natural number with $p \mid M$ and $p^{2} \nmid M$. Let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$ containing every unit $u$ whose image under the reduction map $\mathtt{ZMod.unitsMap}$ to $(\mathbb{Z}/(M/p))^{\times}$ is $1$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense that $p$ belongs to its set of nonunits, and write $I$ for `Pl.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup inside the decomposition subgroup of $Pl$. Let $J_H =$ [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127) be the group of degree-zero divisor classes of the function field [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) over $\overline{\mathbb{Q}}$ (degree-zero divisors modulo principal ones), and let $T$ be its $p$-torsion subgroup, a $\mathbb{Z}/p$-module. Let $b$ be a $\mathbb{Z}/p$-bilinear form on $T$ satisfying the following twisted equivariance: for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every natural number $c$ coprime to $M$ such that $\sigma\zeta = \zeta^{c}$ for all $\zeta$ with $\zeta^{M} = 1$, and for all $x,y,x',y' \in T$ with $x' = \langle c\rangle(\sigma \cdot x)$ and $y' = \sigma \cdot y$ in $J_H$ (where $\langle c \rangle =$ [`ModularCurve.diamondHBar M H`](def/ModularCurve_XHOperators.html#L57) at the unit determined by $c$), one has $b(x',y') = c \cdot b(x,y)$. Finally let $x, y \in T$ be such that for every $\sigma \in I$ and every natural number $c$ with $\sigma\zeta = \zeta^{c}$ for all $p$-th roots of unity $\zeta$, one has $\sigma \cdot x = c\,x$ and $\sigma \cdot y = c\,y$ in $J_H$. Then $b(x,y) = 0$.
--
--   This is the statement that the part of $J_H[p]$ on which inertia at a place above $p$ acts through the mod-$p$ cyclotomic character is totally isotropic for a pairing obeying the diamond-twisted Galois law, in the situation $p \parallel M$ with $H$ containing the kernel of $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$. It is used in the construction of the linear map identifying a dual of the multiplicative submodule of differentials attached to the Néron model of $J_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_bilinForm_apply_eq_zero_of_inertia_cyclotomic.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups

theorem ModularCurve.bilinForm_apply_eq_zero_of_inertia_cyclotomic
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (b : LinearMap.BilinForm (ZMod p) ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p))
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
      ∀ (x y x' y' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (x' : ModularCurve.JH M H) = ModularCurve.diamondHBar M H (ZMod.unitOfCoprime c hc) (σ • (x : ModularCurve.JH M H)) →
        (y' : ModularCurve.JH M H) = σ • (y : ModularCurve.JH M H) →
          b x' y' = (c : ZMod p) • b x y)
    (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) (hx : (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • (x : ModularCurve.JH M H) = c • (x : ModularCurve.JH M H))) (hy : (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • (y : ModularCurve.JH M H) = c • (y : ModularCurve.JH M H))) :
    b x y = 0 := by sorry
