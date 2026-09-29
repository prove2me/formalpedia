-- Prove2me | Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
-- name    : ModularCurve.moduleFinite_padicInt_tateModule_jOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/b59570a8-6349-521e-9864-e18783c04564
-- title:
--   Finite generation of the p-adic Tate module of J₁(M)
-- statement:
--   Let $M$ be a natural number, assumed nonzero, and let $p$ be a prime. Write $\overline{\mathbb Q}$ for the algebraic closure of $\mathbb Q$ used throughout, and let [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186) be the group $\mathrm{Pic}^0$ of the function field [`ModularCurve.x1FunctionFieldBar M`](def/ModularCurve_X1.html#L182), that is, the base change over $\overline{\mathbb Q}$ of the function field of $X_1(M)$ inside the Laurent series field $\overline{\mathbb Q}((q))$: concretely, the quotient of the group of degree-zero divisors of that field over $\overline{\mathbb Q}$ by the subgroup of principal divisors. On an additive commutative group $A$, [`TateModule p A`](def/EllipticCurve_TateModule.html#L15) is defined as the additive subgroup of sequences $x : \mathbb N \to A$ such that $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$, i.e. the inverse limit $\varprojlim_n A[p^n]$ along multiplication by $p$. The assertion is that [`TateModule p (ModularCurve.JOne M)`](def/EllipticCurve_TateModule.html#L15), with its $\mathbb Z_p$-module structure, is a finite $\mathbb Z_p$-module, i.e. finitely generated over $\mathbb Z_p$. Freeness and the precise rank $2g$, $g$ the genus of $X_1(M)$, are not asserted.
--
--   This records the finiteness half of the classical description of the $p$-adic Tate module $T_p J_1(M)$ of the Jacobian of $X_1(M)$, which is free of rank twice the genus. It is used in the Eichler–Shimura construction of $p$-adic Galois representations attached to weight-two eigenforms, where it guarantees that the relevant Hecke and diamond algebras act on a finitely generated $\mathbb Z_p$-lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.moduleFinite_padicInt_tateModule_jOne (M p : ℕ) [NeZero M] [Fact p.Prime] :
    Module.Finite ℤ_[p] (TateModule p (ModularCurve.JOne M)) := by sorry
