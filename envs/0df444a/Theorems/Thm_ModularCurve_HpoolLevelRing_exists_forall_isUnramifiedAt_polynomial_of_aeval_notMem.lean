-- Prove2me | Theorems.Thm_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
-- name    : ModularCurve.HpoolLevelRing.exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/16d1325f-5297-52fe-8d00-c33d67a80bf5
-- title:
--   Unramifiedness of Ogg's unit off a polynomial divisor
-- statement:
--   Fix a prime $p$. Let $F =$ `modularFunctionFieldFull p` be the intermediate field of $\mathbb{Q} \subseteq$ `LaurentSeries ℚ` obtained by adjoining the divisor expansions at level $p$, and assume that the Laurent series `modularUnitSeries p` $= \Delta(q)\,\Delta(q^p)^{-1}$ lies in $F$; write $u$ for the resulting element of $F$. Let `Afin p` be the finite-$j$ chart algebra `chartAlg ℤ F {jFull p}`, the $\mathbb{Z}$-subalgebra of $F$ attached to the element `jFull p` in the two-chart integral model, and let $v \in$ `Afin p` be an element whose image in $F$ is either $u$ or $p^{12}u^{-1}$. Give $\mathbb{Z}[X]$ its algebra structure on `Afin p` through $X \mapsto v$, i.e. via `Polynomial.aeval v`. The assertion is that there exists a nonzero $c_0' \in \mathbb{Z}[X]$ such that for every prime ideal $P$ of `Afin p` whose contraction to $\mathbb{Z}$ is the zero ideal and with $c_0'(v) \notin P$, the algebra `Afin p` is unramified over $\mathbb{Z}[X]$ at $P$, that is, the localisation of `Afin p` at $P$ is formally unramified over $\mathbb{Z}[X]$.
--
--   This is the generic-unramifiedness statement for Ogg's modular unit $\Delta(q)/\Delta(q^p)$ regarded as a map from the finite-$j$ chart of the integral model of $X_0(p)$ to the affine line: in characteristic zero the non-constant function $v$ is separable, hence ramifies only above the finitely many critical values cut out by $c_0'$. It serves as the hypothesis on generic behaviour used by [`ModularCurve.HpoolLevelRing.exists_finite_etale_levelRing_self`](thm.html#ModularCurve.HpoolLevelRing.exists_finite_etale_levelRing_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.lean

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_HpoolLevelRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial ModularCurve ModularCurve.HpoolLevelRing

theorem ModularCurve.HpoolLevelRing.exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p)
    (v : Afin p)
    (hv : (v : ↥(modularFunctionFieldFull p)) = (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p)) ∨
      (v : ↥(modularFunctionFieldFull p)) = (p : ↥(modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p))⁻¹) :
    letI : Algebra ℤ[X] (Afin p) := (Polynomial.aeval v).toRingHom.toAlgebra
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ (P : Ideal (Afin p)) [P.IsPrime],
      P.comap (algebraMap ℤ (Afin p)) = ⊥ → Polynomial.aeval v c₀' ∉ P → Algebra.IsUnramifiedAt ℤ[X] P := by sorry
