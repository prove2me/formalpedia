-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorBar_cuspidalClass
-- name    : ModularCurve.heckeOperatorBar_cuspidalClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/7b818733-57fc-58bc-884c-32e8cb86a500
-- title:
--   T_ℓ multiplies the cuspidal class by 1+ℓ
-- statement:
--   Let $p$ be a prime and let $\ell$ be a prime, given as an element of `Nat.Primes`, with $\ell \neq p$ as natural numbers. The assertion concerns the group $\mathrm{JZero}\,p = \mathrm{Pic}^0$ of the function field `modularFunctionFieldBar p` over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, i.e. the quotient of the group of degree-zero divisors by the subgroup of principal divisors, and the element `cuspidalClass p`, the class of the degree-zero divisor $(\mathrm{cuspZeroBar}\,p) - (\mathrm{cuspInftyBar}\,p)$, the difference of the two cusps. The operator `heckeOperatorBar p ℓ` is the $\mathbb{Z}$-linear endomorphism of this group obtained from the additive map `heckeOperatorAlong (AlgebraicClosure ℚ) p ℓ`, which by definition is the map `heckePic0Bar` attached to the Hecke inputs at level $p$ and index $\ell$ when such inputs exist, and the zero map otherwise. The conclusion is the equality $$\mathrm{heckeOperatorBar}\,p\,\ell\,(\mathrm{cuspidalClass}\,p) = (1+\ell)\cdot \mathrm{cuspidalClass}\,p$$ of elements of $\mathrm{JZero}\,p$, the right-hand side being the integer multiple of the cuspidal class by $1+\ell \in \mathbb{Z}$.
--
--   This is the $T_\ell$ half of the statement that the Eisenstein ideal annihilates the cuspidal class on $J_0(p)$: away from $p$ the Hecke operator acts on the class of $(0)-(\infty)$ as multiplication by $1+\ell$. It is stated in exactly the shape required as a hypothesis of [`ModularCurve.eisensteinKernelKillsCuspidalClass_heckeModuleBar`](thm.html#ModularCurve.eisensteinKernelKillsCuspidalClass_heckeModuleBar), and is used in the derivation that the Eisenstein ideal kills the cuspidal class, as in [`ModularCurve.eisensteinIdeal_smul_cuspidalClass`](thm.html#ModularCurve.eisensteinIdeal_smul_cuspidalClass).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorBar_cuspidalClass.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.heckeOperatorBar_cuspidalClass (p : ℕ) [Fact p.Prime] (ℓ : Nat.Primes) (hl : (ℓ : ℕ) ≠ p) : heckeOperatorBar p ℓ (cuspidalClass p) = (1 + ℓ : ℤ) • cuspidalClass p := by sorry
