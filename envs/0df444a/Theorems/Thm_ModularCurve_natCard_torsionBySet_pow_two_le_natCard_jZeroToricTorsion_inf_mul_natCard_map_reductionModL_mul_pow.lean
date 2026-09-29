-- Prove2me | Theorems.Thm_ModularCurve_natCard_torsionBySet_pow_two_le_natCard_jZeroToricTorsion_inf_mul_natCard_map_reductionModL_mul_pow
-- name    : ModularCurve.natCard_torsionBySet_pow_two_le_natCard_jZeroToricTorsion_inf_mul_natCard_map_reductionModL_mul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/b0d5f541-cae9-5ded-b3f6-9d7e3527b9c1
-- title:
--   Toric and mod-2 reduction bound for I^m-torsion of J₀(p)
-- statement:
--   Let $p$ be a prime such that $2$ divides $n(p)=(p-1)/\gcd(p-1,12)$. Let $A$ and $B$ be valuation subrings of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$ and $2$ a nonunit of $B$, and suppose $B$ satisfies the predicate `ReductionInputsModL B p`, the hypotheses needed to reduce degree-zero divisor classes along the residue map of $B$. Let $I$ be an ideal of the Hecke algebra `HeckeAlg` $=\mathbb Z[X_\ell : \ell \text{ prime}]$ containing $2$, and suppose $\mathfrak P^c\subseteq I$ for some $c$, where $\mathfrak P=$ `eisensteinMaximalIdeal p 2` is the preimage under the evaluation $X_\ell\mapsto$ (Eisenstein system at level $p$) of the ideal $(2)\subseteq\mathbb Z$. Give $J_0(p)=$ `JZero p`, the group of degree-zero divisor classes of the modular function field of level $p$ over $\overline{\mathbb Q}$, its `HeckeAlg`-module structure `heckeModuleBar p`. Then there is a constant $C$ such that for every $m$, writing $H_m$ for the subgroup of elements of $J_0(p)$ annihilated by all of $I^m$, $$\#H_m\le \#\bigl(T_A[2^m]\cap H_m\bigr)\cdot\#\bigl(\mathrm{red}_B(H_m)\bigr)\cdot 2^{C},$$ where $T_A[2^m]=$ `jZeroToricTorsion p A (2^m)` is the intersection of the $2^m$-torsion of $J_0(p)$ with $n(p)\cdot(\text{inertia-invariant points at }A)$, and $\mathrm{red}_B=$ `reductionModL B p` is reduction into the Picard group over the residue field of $B$.
--
--   This is the two-adic counting step in Mazur's analysis of the Eisenstein ideal, stated for an arbitrary ideal $I$ of the Hecke algebra containing $2$ and sandwiched above a power of the mod-$2$ Eisenstein maximal ideal, rather than only for powers of that maximal ideal. It feeds the growth estimate [`ModularCurve.jZeroNeronTorsionSheaf_growth_two_v5`](thm.html#ModularCurve.jZeroNeronTorsionSheaf_growth_two_v5).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_torsionBySet_pow_two_le_natCard_jZeroToricTorsion_inf_mul_natCard_map_reductionModL_mul_pow.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme

theorem ModularCurve.natCard_torsionBySet_pow_two_le_natCard_jZeroToricTorsion_inf_mul_natCard_map_reductionModL_mul_pow
    (p : ℕ) [Fact p.Prime] (h2n : 2 ∣ eisensteinNumerator p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2)
    (hRI : ReductionInputsModL B p)
    (I : Ideal HeckeAlg) (h2I : (2 : HeckeAlg) ∈ I) (c : ℕ) (hI : (eisensteinMaximalIdeal p 2) ^ c ≤ I) :
    letI := heckeModuleBar p
    ∃ C : ℕ, ∀ m : ℕ,
      Nat.card ↥(Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup ≤
        Nat.card ↥(jZeroToricTorsion p A (2 ^ m) ⊓ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup) *
          Nat.card ↥(((Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup).map (reductionModL B p)) * 2 ^ C := by sorry
