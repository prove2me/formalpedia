-- Prove2me | Theorems.Thm_ModularCurve_reductionModL_eq_zero_of_forall_mem_inertiaSubgroupIn_smul_eq_nsmul_of_ne_two
-- name    : ModularCurve.reductionModL_eq_zero_of_forall_mem_inertiaSubgroupIn_smul_eq_nsmul_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/683a4ffd-10a0-53df-a346-ee81e7dc57de
-- title:
--   Cyclotomic q^k-torsion of J₀(N) reduces to zero above q
-- statement:
--   Fix a level $N \ge 1$ and a prime $q$ with $q \neq 2$, and let $A$ be a valuation subring of $\overline{\mathbf Q} =$ `AlgebraicClosure ℚ` such that $q$, viewed in $\overline{\mathbf Q}$, is a nonunit of $A$ (the predicate `LiesOverPrime`, expressing that the place $A$ lies over $q$). The assertion is: for every $k \in \mathbf N$ and every function $n$ from $\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$, realised as the group of $\mathbf Q$-algebra automorphisms $\overline{\mathbf Q} \simeq_{\mathbf Q} \overline{\mathbf Q}$, to $\mathbf N$ with the property that $\sigma(\zeta) = \zeta^{n(\sigma)}$ for all $\sigma$ and all $\zeta \in \overline{\mathbf Q}$ with $\zeta^{q^k} = 1$ (so $n$ represents the cyclotomic character modulo $q^k$), and for every element $x$ of `JZero N`, the group of degree-zero divisor classes of the base change to $\overline{\mathbf Q}$ of the full modular function field of level $N$, such that $q^k \cdot x = 0$ and $\sigma \cdot x = n(\sigma) \cdot x$ for every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$ of the inertia subgroup of the decomposition subgroup of $A$, one has $\mathrm{reductionModL}\,A\,N\,(x) = 0$, where `reductionModL` is the additive reduction map from `JZero N` to the degree-zero divisor class group of the modular function field of level $N$ over the residue field of $A$.
--
--   This is the statement that $q$-power torsion of multiplicative type in $J_0(N)$, i.e. torsion on which inertia at a place above an odd prime $q$ acts through the cyclotomic character, lies in the kernel of reduction at that place. It is used in the comparison of Hecke torsion subgroups with their images under reduction, in particular in the counting results [`ModularCurve.natCard_heckeTorsion_span_sup_eq_natCard_heckeLatticeAlgebra_quotient_mul_natCard_inertia_smul_eq_nsmul_of_ne_two`](thm.html#ModularCurve.natCard_heckeTorsion_span_sup_eq_natCard_heckeLatticeAlgebra_quotient_mul_natCard_inertia_smul_eq_nsmul_of_ne_two) and [`ModularCurve.natCard_image_reductionModL_heckeTorsion_span_sup_le_natCard_heckeLatticeAlgebra_quotient`](thm.html#ModularCurve.natCard_image_reductionModL_heckeTorsion_span_sup_le_natCard_heckeLatticeAlgebra_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_reductionModL_eq_zero_of_forall_mem_inertiaSubgroupIn_smul_eq_nsmul_of_ne_two.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.reductionModL_eq_zero_of_forall_mem_inertiaSubgroupIn_smul_eq_nsmul_of_ne_two
    (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∀ k : ℕ, ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
      (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ k) = 1 → σ ζ = ζ ^ n σ) →
      ∀ x : JZero N, (q ^ k) • x = 0 →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = n σ • x) →
        reductionModL A N x = 0 := by sorry
