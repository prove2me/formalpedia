-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries
-- name    : ModularCurve.JHPlaceSpecialization.isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/c4cccc05-650b-5203-b1b8-0e0c579904bc
-- title:
--   Places with nonzero order at Δ(q)/Δ(qᵖ) are cuspidal
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$. Work inside $F =$ `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the function field `xHFunctionField M H`, realised as an intermediate field of $\overline{\mathbb{Q}} \subseteq \mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ through $q$-expansions. Let $u \in F$ be an element whose underlying Laurent series is the coefficientwise image under $\mathbb{Q} \to \overline{\mathbb{Q}}$ of `modularUnitSeries p`, the series $\Delta(q)\,\Delta(q^{p})^{-1}$. Let $V$ be a place of $F$ over $\overline{\mathbb{Q}}$, that is, a valuation subring of $F$ other than $F$ itself which contains the image of $\overline{\mathbb{Q}}$ and is a principal ideal ring, and suppose that the associated order $\mathrm{ord}_V(u)$, defined as minus the logarithm of the adic valuation attached to $V$, is nonzero. The conclusion is that $V$ is cuspidal in the sense of `JHPlaceSpecialization.IsCuspidal`: for every $x \in F$ whose underlying Laurent series is `jqModC` over $\overline{\mathbb{Q}}$, the $q$-expansion of $j$, and every $a \in A$, one has $\mathrm{ord}_V\bigl(x - a\bigr) \le 0$, where $a$ is viewed in $F$ through the structure map from $\overline{\mathbb{Q}}$.
--
--   This is the statement that the modular unit $\Delta(q)/\Delta(q^{p})$ on $X_H(M)$ has zeros and poles only at places at which $j$ takes no $A$-integral value, i.e. only at the cusps. It serves as an avoidance step in the analysis of the specialisation of places and divisor classes of $X_H(M)$ at $p$, and is used in the construction of vertical units and one-sided laws for models of $X_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (u : ↥(xHFunctionFieldBar M H))
    (hu : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV : V.ord u ≠ 0) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V := by sorry
