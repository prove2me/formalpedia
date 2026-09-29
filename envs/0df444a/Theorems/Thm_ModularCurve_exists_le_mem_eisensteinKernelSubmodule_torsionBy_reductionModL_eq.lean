-- Prove2me | Theorems.Thm_ModularCurve_exists_le_mem_eisensteinKernelSubmodule_torsionBy_reductionModL_eq
-- name    : ModularCurve.exists_le_mem_eisensteinKernelSubmodule_torsionBy_reductionModL_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/0c99f279-d7ec-5d3f-af3c-29ec0d5ce0de
-- title:
--   Lifting ℓ-power torsion in the Eisenstein kernel through reduction
-- statement:
--   Fix $p\ge 1$ (a natural number with `NeZero p`) and assume `HeckeOperatorsCommuteBar p`, i.e. the operators $\bar T_\ell$ on $J_0(p)$ — the degree-zero divisor class group $\mathrm{Pic}^0$ of the modular function field of level $p$ over $\overline{\mathbb Q}$, written `JZero p` — commute for all pairs of primes; this makes `JZero p` a module over $\mathbb T=\mathbb Z[T_\ell:\ell\text{ prime}]$ via `heckeModuleBar p`. Let $\ell$ be a prime with $\ell\nmid p$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, whose residue field has characteristic $\ell$, and assume the reduction data `ReductionInputsModL A p` for level $p$ along the residue map of $A$. Let $k\in\mathbb N$ and $y\in$ `eisensteinKernelSubmodule p`, the $\mathbb T$-submodule $\gamma\cdot J_0(p)$ obtained by acting on all of `JZero p` by the ideal $\{t\in\mathbb T:\exists\, i\in I_{\mathrm{Eis}},\ (1+i)t\ \text{annihilates}\ J_0(p)\}$, where $I_{\mathrm{Eis}}$ is the Eisenstein ideal. Suppose the reduction $\mathrm{red}_A(y)$ in $J_0(p)$ over the residue field of $A$ is killed by $\ell^k$. Then there are $n\ge k$ and $z\in\gamma\cdot J_0(p)$ with $\ell^n z=0$ and $\mathrm{red}_A(z)=\mathrm{red}_A(y)$.
--
--   This is the reduction-theoretic input at a place above $\ell\nmid p$ which allows an $\ell$-power torsion class in the reduction of the Eisenstein kernel to be represented by a genuine $\ell$-power torsion point of the Eisenstein kernel, at the cost of raising the exponent from $k$ to some $n\ge k$. It is used in the construction of finite flat models for the $\ell^k$-torsion of the Eisenstein quotient of $J_0(p)$, and rests on the good-reduction abelian scheme model of $J_0(p)$ over the localisation of $\mathbb Z$ at $\ell$ together with the finiteness of multiplication by $\ell^k$ and the finiteness of order of points over the residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_le_mem_eisensteinKernelSubmodule_torsionBy_reductionModL_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve IsLocalRing
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_le_mem_eisensteinKernelSubmodule_torsionBy_reductionModL_eq
    (p : ℕ) [NeZero p] (hcomm : HeckeOperatorsCommuteBar p)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ]
    (hinp : ReductionInputsModL A p)
    (k : ℕ) (y : JZero p)
    (hy : letI := heckeModuleBar p; y ∈ eisensteinKernelSubmodule p (heckeModuleBar p))
    (hred : reductionModL A p y ∈
      Submodule.torsionBy ℤ (JZeroC (ResidueField ↥A) p) ((ℓ : ℤ) ^ k)) :
    letI := heckeModuleBar p
    ∃ n : ℕ, k ≤ n ∧ ∃ z : JZero p, z ∈ eisensteinKernelSubmodule p (heckeModuleBar p) ∧
      z ∈ Submodule.torsionBy ℤ (JZero p) ((ℓ : ℤ) ^ n) ∧
      reductionModL A p z = reductionModL A p y := by sorry
