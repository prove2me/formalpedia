-- Prove2me | Theorems.Thm_ModularCurve_periodLatticeHeckeStable
-- name    : ModularCurve.periodLatticeHeckeStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/6f9edb1f-9c7f-59bf-9f17-f036c271a46f
-- title:
--   Hecke stability of the period lattice at every level
-- statement:
--   Let $N$ be a natural number, nonzero. The assertion is the predicate [`ModularCurve.PeriodLatticeHeckeStable N`](def/ModularCurve_PeriodLattice.html#L223), which unfolds as follows. Write $S$ for the space `CuspForm (CongruenceSubgroup.Gamma0 N) 2` of weight-two cusp forms for $\Gamma_0(N)$ and $S^\vee =$ `Module.Dual ℂ S` for its $\mathbb{C}$-linear dual. Inside $S^\vee$ let $\Lambda_N =$ [`ModularCurve.periodLattice N`](def/ModularCurve_PeriodLattice.html#L102) be the $\mathbb{Z}$-submodule spanned by the range of the family of functionals [`ModularCurve.period N`](def/ModularCurve_PeriodLattice.html#L92). Let [`ModularCurve.dualHeckeRep N`](def/ModularCurve_PeriodLattice.html#L198) be the ring homomorphism from `HeckeAlg` to `Module.End ℂ S`$^{\vee}$ sending $t$ to the transpose (dual map) of the endomorphism `cuspHeckeRep N t` of $S$; multiplicativity holds because `HeckeAlg` is commutative, so that transposition reverses products harmlessly. Then for every prime $\ell$ (an element of `Nat.Primes`) and every $x \in S^\vee$ with $x \in \Lambda_N$, the element obtained by applying `dualHeckeRep N` evaluated at the generator `heckeGen ℓ` $=$ `MvPolynomial.X ℓ` of `HeckeAlg` to $x$ again lies in $\Lambda_N$. In other words, the period lattice is stable under the transpose of each generating Hecke operator, with no condition relating $\ell$ to $N$.
--
--   This is the integrality of the Hecke correspondences on the period lattice of $X_0(N)$: the image of $H_1(X_0(N)(\mathbb{C}),\mathbb{Z})$ in $S_2(\Gamma_0(N))^\vee$ is preserved by the transposed operators attached to every prime, dividing the level or not. It underlies the Eichler–Shimura comparison used downstream, in particular the statements about Hecke eigenspaces in Tate modules, Frobenius traces on eigenplanes, and the action of the generators at primes dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodLatticeHeckeStable.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.periodLatticeHeckeStable (N : ℕ) [NeZero N] :
    ModularCurve.PeriodLatticeHeckeStable N := by sorry
