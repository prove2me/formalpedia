-- Prove2me | Theorems.Thm_ModularCurve_qExpFrobeniusPushforwardModL_eq_qExpArithFrobC_smul
-- name    : ModularCurve.qExpFrobeniusPushforwardModL_eq_qExpArithFrobC_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/ac16ef49-06e2-5ad0-b5c0-a9cfd948cbf7
-- title:
--   Frobenius push-forward on Pic⁰ is arithmetic Frobenius
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$, and let $\bar F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) be the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the quotients `intSeriesC K pf / intSeriesC K pg` of reductions of integral $q$-expansions of modular forms of weight $k$ for $\Gamma$. Assume `hx`: there is $x \in \bar F$ transcendental over $K$ such that $\bar F$ is finite-dimensional over $K(x)$. Let $z$ be an element of $\mathrm{Pic}^0(\bar F/K)$, that is, of the quotient of the group of finitely supported $\mathbb{Z}$-valued functions on the places of $\bar F$ over $K$ of total degree zero by its subgroup of principal divisors. Then the endomorphism [`ModularCurve.qExpFrobeniusPushforwardModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L243) of $\mathrm{Pic}^0$ — the push-forward of degree-zero divisor classes along `qExpFrobeniusModL K Γ p`, defined to be the induced map on the quotient when the data `QExpFrobeniusInputsModL` (existence of principal divisors, finiteness along the map, the fundamental identity and the norm formula) are available, and $0$ otherwise — sends $z$ to $\sigma \cdot z$, where $\sigma =$ [`ModularCurve.qExpArithFrobC p K Γ`](def/ModularCurve_QExpCoeffSemilinearAut.html#L188) is the semilinear automorphism of $\bar F$ over $K$ given by the pair consisting of the coefficientwise $p$-th power map on $q$-expansions and the Frobenius of $K$, acting on $\mathrm{Pic}^0$ through its action on places.
--
--   This identifies the geometric Frobenius push-forward on the Jacobian of the reduction of the modular curve with the action of the arithmetic Frobenius, the comparison underlying the Eichler–Shimura relation in characteristic $p$. It is used in the comparison of degeneracy maps and points in the model of $X_H$ at $p$, and in the proof that the Frobenius push-forward acts with finite order on classes fixed by all power maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFrobeniusPushforwardModL_eq_qExpArithFrobC_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.qExpFrobeniusPushforwardModL_eq_qExpArithFrobC_smul
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hx : ∃ x : ModularCurve.qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ))
    (z : Pic0 K (ModularCurve.qExpFunctionFieldC K Γ)) :
    ModularCurve.qExpFrobeniusPushforwardModL K Γ p z = ModularCurve.qExpArithFrobC p K Γ • z := by sorry
