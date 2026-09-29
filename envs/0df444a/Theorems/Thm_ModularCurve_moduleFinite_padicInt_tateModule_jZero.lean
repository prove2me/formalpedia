-- Prove2me | Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero
-- name    : ModularCurve.moduleFinite_padicInt_tateModule_jZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/9b4f8efd-b58f-5e99-9062-1ea6304476cc
-- title:
--   Finite generation of the p-adic Tate module of J₀(N)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $p$ be a prime. Write $\bar F_N$ for the intermediate field `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full level-$N$ modular function field inside the field of Laurent series over $\overline{\mathbb Q}$, and let [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115) be the group $\mathrm{Pic}^0(\overline{\mathbb Q}, \bar F_N)$, namely the group of divisors of degree zero of $\bar F_N$ over $\overline{\mathbb Q}$ modulo the subgroup of principal divisors (an incarnation of $J_0(N)(\overline{\mathbb Q})$). For an abelian group $M$, [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) is the subgroup of the group of sequences $x \colon \mathbb N \to M$ consisting of those $x$ satisfying $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for every $n$, i.e. the inverse limit of the $p^n$-torsion subgroups along multiplication by $p$, carrying its $\mathbb Z_p$-module structure. The assertion is that [`TateModule p (ModularCurve.JZero N)`](def/EllipticCurve_TateModule.html#L15) is a finitely generated $\mathbb Z_p$-module. Only finite generation over $\mathbb Z_p$ is asserted, not freeness or the value $2g$ of the rank.
--
--   This is the finiteness half of the classical description of the $p$-adic Tate module of the Jacobian $J_0(N)$, and rests on the count of $p^n$-torsion in the degree-zero divisor class group of a curve ([`AlgebraicCurve.Pic0.abelJacobiCard_genus`](thm.html#AlgebraicCurve.Pic0.abelJacobiCard_genus)) applied to the modular function field of level $N$, which is a curve over $\overline{\mathbb Q}$ with a canonical divisor and is finite over a rational subfield. It is used in the construction of the $\lambda$-adic Galois representations attached to newforms, where the image of the Tate module after tensoring with a coefficient ring must be recognised as a lattice in a two-dimensional space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.moduleFinite_padicInt_tateModule_jZero (N p : ℕ) [NeZero N] [Fact p.Prime] :
    Module.Finite ℤ_[p] (TateModule p (ModularCurve.JZero N)) := by sorry
