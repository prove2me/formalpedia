-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi
-- name    : ModularCurve.XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/ffa615b4-7adc-5e9c-8a5f-3a58338409ef
-- title:
--   Finiteness and finite presentation of π for X_H(M) at p‖M
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ but $p^2 \nmid M$, and with $M/p$ nonzero, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing the kernel of the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, i.e. every unit $u$ with `ZMod.unitsMap` image $1$ along $M/p \mid M$ lies in $H$. Assume $j$, in the form of the Laurent series `jqModC ℚ` $= q^{-1}\cdot\mathrm{jNum}$ over $\mathbb{Q}$, lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients $\mathrm{(int.\ }q\mathrm{-exp\ of\ }f)/\mathrm{(int.\ }q\mathrm{-exp\ of\ }g)$ of integral $q$-expansions of modular forms for the full modular group. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which packages integral models over the ring `R p` for levels $\Gamma_H(M)$ and $\Gamma_{H'}(M/p)$ together with properness, flatness, integrality, local finite presentation, normality on affine opens, smoothness of relative dimension $1$ in the level-$(M/p)$ and generic fibres, geometric integrality, a curve model of the geometric function field over $\overline{\mathbb{Q}}$ with Galois-equivariant identification and $q$-expansion normalisation, and a morphism datum `π` between the models (the remaining fields being summarised here). The conclusion is that the underlying scheme morphism `𝔛.π.1` is finite and locally of finite presentation.
--
--   This is the finiteness assertion for the degeneracy (forgetful) morphism between the Deligne–Rapoport style integral models of $X_H(M)$ and of the level-$\Gamma_{H'}(M/p)$ curve at a prime exactly dividing the level. It feeds [`ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi`](thm.html#ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi), where finiteness is upgraded to flatness together with a bound on the rank of the corresponding module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    IsFinite 𝔛.π.1 ∧ LocallyOfFinitePresentation 𝔛.π.1 := by sorry
