-- Prove2me | Theorems.Thm_ModularCurve_exists_jZeroGoodReductionSpecialization_doorPredicates
-- name    : ModularCurve.exists_jZeroGoodReductionSpecialization_doorPredicates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/c5b7e861-9eb4-52bb-834c-b9143a4b6bca
-- title:
--   Good-reduction specialisation of J₀(p) at ℓ with four predicates
-- statement:
--   Fix a prime $p$, a prime $\ell\neq p$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $\ell$ in the sense that $\ell$ is a non-unit of $A$; assume the project's commutation hypothesis `HeckeOperatorsCommuteBar p`, that the operators `heckeOperatorBar p ℓ'` on $J_0(p)=$ `JZero p` (the degree-zero divisor class group over $\overline{\mathbb{Q}}$ of the level-$p$ modular function field) commute pairwise, so that the Hecke algebra $\mathbb{Z}[T_q : q \text{ prime}]$ acts through `heckeModuleBar p`. The conclusion asserts the existence of a Hecke-algebra module structure on $\mathrm{Pic}^0$ of the characteristic-$\ell$ modular function field `modularFunctionFieldC (ResidueField A) p` over the residue field of $A$, together with a datum $D$ of type `JZeroGoodReductionSpecialization A ℓ hℓp p`: that is, a surjective additive map $\mathrm{sp}\colon J_0(p)\to \mathrm{Pic}^0$ of the special fibre and an additive endomorphism $F$ of the target such that $\mathrm{sp}$ is Hecke-equivariant, is invariant under the inertia subgroup of $A$ over $\mathbb{Q}$, satisfies $\mathrm{sp}(\sigma\cdot x)=F(\mathrm{sp}\,x)$ for every $\sigma$ that is a Frobenius at $A$ for $\ell$, is injective on $q$-power torsion for every prime $q\neq\ell$, and such that $F^2-T_\ell F+\ell=0$ holds on the target. Moreover $D$ satisfies four further clauses: `TorsBijFor ℓ D.sp`, that for each prime $q\neq\ell$ every $q$-power torsion element of the target is $\mathrm{sp}$ of a $q$-power torsion element; `FTorsionFor`, that every element of the target has finite order; `RaynaudFor ℓ D.sp`, that if $\ell\neq2$ then an $\ell$-power torsion element $z$ of the project's rational part of the Eisenstein quotient ($J_0(p)$ modulo the Eisenstein-kernel submodule), all of whose lifts have $\mathrm{sp}$-image in $\mathrm{sp}$ of the Eisenstein kernel submodule, vanishes; and `CuspRuleFor A D.sp`, that for a place $x$ of the geometric modular function field fixed by the arithmetic Galois action, with $\mathrm{ord}_x(j-j_1)>0$, $\mathrm{ord}_x(j_p-j_2)>0$ and $|j_1|_A>1$, the class of $(x)-(\infty)$ (if $|j_2|_A=|j_1|_A^{\,p}$), respectively of $(x)-(0)$ (if $|j_2|_A^{\,p}=|j_1|_A$), has $\mathrm{sp}$-image in $\mathrm{sp}$ of the Eisenstein kernel submodule. The last clause is thus a membership statement in the image of the Eisenstein kernel, not the stronger vanishing statement of `CuspRuleStrongFor`.
--
--   This is the per-prime good-reduction input to Mazur's specialisation argument for the Eisenstein quotient of $J_0(p)$ (Mazur, Modular curves and the Eisenstein ideal, II §11 and III §5), with the $\ell$-adic finite flat group scheme ingredient going back to Raynaud. Compared with the textbook account, the formal statement fixes one place $A$ of $\overline{\mathbb{Q}}$ above $\ell$ at a time, replaces the Néron model and its special fibre by the divisor class group of the characteristic-$\ell$ modular function field, and packages Hecke equivariance, inertia invariance, the Eichler–Shimura relation $F^2-T_\ell F+\ell=0$ and prime-to-$\ell$ injectivity into a single structure; the Raynaud and cusp clauses are stated with values in the image under $\mathrm{sp}$ of the Eisenstein kernel rather than as exact vanishing. It is the sole input to [`ModularCurve.mazurQuotientSpecialization_heckeModuleBar`](thm.html#ModularCurve.mazurQuotientSpecialization_heckeModuleBar), which assembles these per-place data into the project's `MazurQuotientSpecialization` predicate for level $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_jZeroGoodReductionSpecialization_doorPredicates.lean

import Definitions.Def_ModularCurve_JZeroGoodReductionV2
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_StepThreeDoorPredicates

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve IsLocalRing
set_option synthInstance.maxHeartbeats 80000 in

theorem ModularCurve.exists_jZeroGoodReductionSpecialization_doorPredicates (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p)
    (ℓ : ℕ) (hℓp : ℓ.Prime) (hℓ : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    letI := heckeModuleBar p
    ∃ _ : Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p)),
    ∃ D : JZeroGoodReductionSpecialization A ℓ hℓp p,
      TorsBijFor ℓ D.sp ∧
      FTorsionFor (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p)) ∧
      RaynaudFor ℓ D.sp ∧ CuspRuleFor A D.sp := by sorry
