-- Prove2me | Theorems.Thm_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow
-- name    : ModularCurve.hasSum_cosetSubst_coeff_mul_qParam_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/1564c785-f899-5a2b-adaf-c30e4fa577bc
-- title:
--   q-expansion at the coset point (aτ+b)/d
-- statement:
--   Let $N,a,b,d$ be natural numbers with $N \neq 0$, $a \neq 0$ and $a d = N$, let $\zeta$ be a unit of $\mathbb{C}$ whose underlying complex number is $\exp(2\pi i/N)$, let $S$ be a Laurent series over $\mathbb{C}$ (a Hahn series indexed by $\mathbb{Z}$), and let $\tau, x \in \mathbb{C}$. Here $q$-parameters are taken in the form `Function.Periodic.qParam` $h\,z = \exp(2\pi i z/h)$, so that the hypothesis reads: the family $m \mapsto S_m\, e^{2\pi i m(a\tau+b)/d}$, indexed by $m \in \mathbb{Z}$, is summable with sum $x$. The conclusion asserts the same for the coset substitution of $S$: writing $t = e^{2\pi i \tau/N}$, the family $m \mapsto (\mathrm{cosetSubst}\,\zeta\,a\,b\,S)_m\, t^m$ is summable with the same sum $x$, where [`ModularCurve.cosetSubst`](def/ModularCurve_PhiGen.html#L111) is the ring endomorphism of $\mathbb{C}((q))$ obtained by first twisting coefficients, $S_m \mapsto \zeta^{abm} S_m$ (the map `qTwist` with unit $\zeta^{ab}$), and then rescaling the index by $a^2$ (the map `qExpand`, which sends the coefficient in degree $m$ to degree $a^2 m$ and puts $0$ in degrees not divisible by $a^2$). Thus formally $\mathrm{cosetSubst}\,\zeta\,a\,b\,S$ is the series $S(\zeta^{ab} t^{a^2})$ in the variable $t$.
--
--   This is the elementary reindexing identity underlying the statement that the $q$-expansion of a modular function evaluated at the coset representative $(a\tau+b)/d$, with $ad = N$, is obtained from its $q$-expansion by the substitution $q \mapsto \zeta^{ab} q^{a^2}$ with $\zeta = e^{2\pi i/N}$ and $q = e^{2\pi i \tau/N}$. It is used to identify the $q$-expansion of a coset translate with the algebraic operation `cosetSubst` on Laurent series, in [`ModularCurve.qExpansion_cosetTranslate_eq_cosetSubst`](thm.html#ModularCurve.qExpansion_cosetTranslate_eq_cosetSubst).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane

theorem ModularCurve.hasSum_cosetSubst_coeff_mul_qParam_pow {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N)
    [NeZero a] (ζ : ℂˣ) (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (S : LaurentSeries ℂ) (τ : ℂ) (x : ℂ)
    (h : HasSum (fun m : ℤ => S.coeff m * Function.Periodic.qParam 1 ((a * τ + b) / d) ^ m) x) :
    HasSum (fun m : ℤ => (ModularCurve.cosetSubst ζ a b S).coeff m * Function.Periodic.qParam N τ ^ m) x := by sorry
