-- Prove2me | Theorems.Thm_ModularCurve_surjOn_reductionModL_torsion_of_not_dvd
-- name    : ModularCurve.surjOn_reductionModL_torsion_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/39705265-cb87-5727-942e-4f19c5245d68
-- title:
--   Prime-to-ℓ torsion lifts along reduction mod ℓ
-- statement:
--   Let $N \geq 1$ and let $\ell$ be a prime not dividing $N$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ which lies over $\ell$ in the sense of `LiesOverPrime`, that is, the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$, and assume `ReductionInputsModL A N`: there exists an assignment $r$ of places of the base change of the modular function field `modularFunctionFieldFull N` to $\overline{\mathbb{Q}}$ satisfying `IsPlaceReductionAlong A (residue A) N r`, together with `PrincipalGeneratedByIntegral A (residue A) N`, these being the data out of which the reduction homomorphism along the residue map of $A$ is built. Write `reductionModL A N` for the resulting additive homomorphism from `JZero N`, the group of degree-zero divisor classes (degree-zero divisors modulo principal divisors) of the base-changed modular function field over $\overline{\mathbb{Q}}$, to `JZeroC (ResidueField A) N`, the corresponding degree-zero divisor class group formed over the residue field of $A$ from the field generated there by the divisor expansions. Then for every natural number $n$ not divisible by $\ell$, `reductionModL A N` maps the set of $x$ with $n \cdot x = 0$ in `JZero N` onto the set of $y$ with $n \cdot y = 0$ in `JZeroC (ResidueField A) N`; i.e. every $n$-torsion class over the residue field is the image of an $n$-torsion class in characteristic zero.
--
--   This is the surjectivity of reduction on prime-to-$\ell$ torsion for the Jacobian of the modular curve of level $N$ at a place over a prime $\ell$ of good reduction, the standard consequence of the fact that multiplication by $n$ is finite flat on a good model when $\ell \nmid n$ together with the henselian property of the valuation ring of an algebraically closed field. It feeds the counting of torsion in the special fibre, the construction of compatible families of reductions, and the specialisation of divisor classes used in the analysis of torsion of $J_0(N)$ modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_surjOn_reductionModL_torsion_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IsLocalRing

theorem ModularCurve.surjOn_reductionModL_torsion_of_not_dvd
    (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (hinp : ReductionInputsModL A N)
    (n : ℕ) (hℓn : ¬ ℓ ∣ n) :
    Set.SurjOn (reductionModL A N)
      {x : JZero N | n • x = 0}
      {y : JZeroC (ResidueField ↥A) N | n • y = 0} := by sorry
