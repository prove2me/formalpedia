-- Prove2me | Theorems.Thm_ModularCurve_qExpansion_cosetTranslate_eq_cosetSubst
-- name    : ModularCurve.qExpansion_cosetTranslate_eq_cosetSubst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/b9042a80-b731-5ed5-a098-a8ddb53bd19d
-- title:
--   q-expansion of F((aτ+b)/d) as a coset substitution
-- statement:
--   Let $N,a,b,d$ be natural numbers with $N\neq 0$, $a\,d=N$ and $a$ nonzero, and let $\zeta\in\mathbb{C}^{\times}$ be the unit whose underlying complex number is $\exp(2\pi i/N)$. Let $F,G:\mathfrak{H}\to\mathbb{C}$ be functions on the upper half-plane such that: $F$, extended to $\mathbb{C}$ by `UpperHalfPlane.ofComplex`, is periodic with period $1$; $F$ is holomorphic in the sense of being differentiable for the trivial model with corners on $\mathbb{C}$; $F$ is bounded as $\operatorname{Im}\tau\to\infty$; and $G$ is related to $F$ by $G(\tau)=F(\tau')$ whenever $\tau,\tau'\in\mathfrak{H}$ satisfy $\tau'=(a\tau+b)/d$ as complex numbers. The conclusion is a fourfold conjunction: the extension of $G$ is periodic with period $N$; $G$ is holomorphic in the same sense; $G$ is bounded at $i\infty$; and the Laurent series attached to the $q$-expansion of $G$ with respect to $q=\exp(2\pi i\tau/N)$ equals [`ModularCurve.cosetSubst`](def/ModularCurve_PhiGen.html#L111) $\zeta\,a\,b$ applied to the Laurent series attached to the $q$-expansion of $F$ at period $1$, i.e. the series obtained from $\sum_m c_m t^m$ by replacing it with $\sum_m c_m\zeta^{abm}t^{a^2m}$ (multiply the $m$-th coefficient by $\zeta^{abm}$, then dilate exponents by $a^2$).
--
--   This is the classical computation that, for $N=ad$, the function $\tau\mapsto F((a\tau+b)/d)$ is $N$-periodic with $q^{1/N}$-expansion obtained from that of $F$ by the substitution $q\mapsto\zeta^{ab}t^{a^2}$, together with the regularity needed to treat it as an expansion at the cusp. It is used to identify the formal coset conjugates occurring in the modular polynomial and in the $q$-expansion principle for function fields of $X_0$ and $X_H$ with genuine expansions of translated modular functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansion_cosetTranslate_eq_cosetSubst.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane

theorem ModularCurve.qExpansion_cosetTranslate_eq_cosetSubst {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N)
    [NeZero a] (ζ : ℂˣ) (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (F G : ℍ → ℂ) (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1) (hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F)
    (hFbd : UpperHalfPlane.IsBoundedAtImInfty F)
    (hG : ∀ τ τ' : ℍ, ((τ' : ℂ) = ((a : ℂ) * τ + b) / d) → G τ = F τ') :
    Function.Periodic (G ∘ UpperHalfPlane.ofComplex) N ∧ MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) G ∧ UpperHalfPlane.IsBoundedAtImInfty G ∧
      ((qExpansion N G : PowerSeries ℂ) : LaurentSeries ℂ)
        = ModularCurve.cosetSubst ζ a b ((qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ) := by sorry
