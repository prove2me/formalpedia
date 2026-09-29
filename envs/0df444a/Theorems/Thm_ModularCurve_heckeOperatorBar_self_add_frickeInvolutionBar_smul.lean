-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorBar_self_add_frickeInvolutionBar_smul
-- name    : ModularCurve.heckeOperatorBar_self_add_frickeInvolutionBar_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/276a4c0d-5c20-504f-b946-b72bca8f35b8
-- title:
--   Prime level: Uₚ + w = 0 on J₀(p)
-- statement:
--   Let $p$ be a prime. Write $F_p$ for the subfield of the Laurent series field over $\mathbb{Q}$ generated over $\mathbb{Q}$ by the family `divisorExpansions p` (the $q$-expansion model of the function field of $X_0(p)$), and let $\overline{F}_p$ be its base change `modularFunctionFieldBar p` to $\overline{\mathbb{Q}}$, an intermediate field of the Laurent series field over the algebraic closure of $\mathbb{Q}$; `JZero p` is the group $\mathrm{Pic}^0$ of $\overline{F}_p$ over $\overline{\mathbb{Q}}$, that is, degree-zero divisors modulo principal divisors. Two operators on this group are compared: `heckeOperatorBar p` evaluated at the prime $p$ itself, namely the $\mathbb{Z}$-linear endomorphism coming from `heckeOperatorAlong` at level $p$ and prime $p$ (the correspondence-induced map built from the Hecke data when the predicate `HeckeInputsAlong` holds, and $0$ otherwise); and the action of `frickeInvolutionBar p`, the $\overline{\mathbb{Q}}$-automorphism of $\overline{F}_p$ obtained by base change from a chosen $\mathbb{Q}$-automorphism of $F_p$ satisfying `IsFrickeAutFull` (the identity if none exists), acting on divisor classes. The assertion is that for every $x \in$ `JZero p` one has $U_p x + w \cdot x = 0$.
--
--   This is the Atkin–Lehner relation $U_p = -w$ at prime level, stated on divisor classes of $X_0(p)$ over $\overline{\mathbb{Q}}$ (on divisors it fails, the left-hand side having degree $p+1$). It is what reconciles the two standard generating sets of the Eisenstein ideal in the image of the Hecke algebra in $\mathrm{End}(J_0(p))$, and is used in the treatment of the Eisenstein quotient and in identifying Hecke fibres with the Fricke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorBar_self_add_frickeInvolutionBar_smul.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.heckeOperatorBar_self_add_frickeInvolutionBar_smul (p : ℕ)
    [Fact p.Prime] :
    ∀ x : JZero p, heckeOperatorBar p ⟨p, Fact.out⟩ x + frickeInvolutionBar p • x = 0 := by sorry
