-- Prove2me | Theorems.Thm_ModularCurve_exists_natCard_heckeLatticeAlgebra_quotient_span_pow_sup_pow_le_natCard_eisensteinPrimaryTorsionBar_quotient_mul_pow
-- name    : ModularCurve.exists_natCard_heckeLatticeAlgebra_quotient_span_pow_sup_pow_le_natCard_eisensteinPrimaryTorsionBar_quotient_mul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/5ee5d64a-89b3-5be8-93b0-68bdb45d6462
-- title:
--   Mazur-type bound on T^L/((q^m)+(P^L)^M) for large M
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$ and $q \neq p$, and let $A_q$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ belongs to the nonunits of $A_q$. Then there is a natural number $C$ such that for all natural numbers $m$ and $M_1$ there is $M \geq M_1$ with the following property. Let $n \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathbb N$ be any function with $\sigma\zeta = \zeta^{n(\sigma)}$ for every automorphism $\sigma$ and every $\zeta \in \overline{\mathbb Q}$ with $\zeta^{q^m} = 1$ (a choice of exponents for the mod $q^m$ cyclotomic character). Let $W$ be an additive subgroup of `JZero p`, the group of degree-zero divisor classes modulo principal divisors of the modular function field of level $p$ over $\overline{\mathbb Q}$, such that: $W$ is contained in $E :=$ the intersection of the kernel of multiplication by $q^m$ with the supremum over $k$ of the submodules of `JZero p` annihilated by the $k$-th power of the Eisenstein ideal $\mathfrak P =$ `eisensteinMaximalIdeal p q` (the preimage of $(q)$ under the Eisenstein evaluation map on $\mathbb T =$ `HeckeAlg`); $\sigma \cdot x = n(\sigma)\,x$ for all $x \in W$ and all $\sigma$ in the inertia subgroup of $A_q$ inside $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (the image of the inertia subgroup in the decomposition subgroup); and $\sigma \cdot x - x \in W$ for all such $\sigma$ and all $x \in E$. Then the cardinality of the quotient of the lattice Hecke algebra `heckeLatticeAlgebra p ∅` — the image of the weight-two level-$p$ Hecke algebra in $\mathrm{End}_{\mathbb Z}$ of the integral lattice `intLattice p 2` — by the ideal $(q^m) + (\mathfrak P^L)^M$, where $\mathfrak P^L$ is the image of $\mathfrak P$ under `heckeEvalForms p 2` followed by `latticeRestrictHom p ∅`, is at most the cardinality of $E/W$ multiplied by $q^C$.
--
--   This is a counting bound of the kind appearing in Mazur's study of the Eisenstein ideal: the congruence quotients of the lattice Hecke algebra in the $(q^m, \mathfrak P^M)$-currency are bounded, up to a fixed power of $q$, by the quotient of the $\mathfrak P$-primary $q^m$-torsion of $J_0(p)$ by a subgroup on which inertia at $q$ acts through the cyclotomic character and which absorbs all inertia displacements. It is used in the linear-growth estimate [`ModularCurve.jZeroNeronTorsionSheaf_inv_linearGrowth_v5`](thm.html#ModularCurve.jZeroNeronTorsionSheaf_inv_linearGrowth_v5) for the torsion sheaf attached to $J_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_natCard_heckeLatticeAlgebra_quotient_span_pow_sup_pow_le_natCard_eisensteinPrimaryTorsionBar_quotient_mul_pow.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_ModularCurve_MultiplicativeType
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CuspForm
open ModularCurve

theorem ModularCurve.exists_natCard_heckeLatticeAlgebra_quotient_span_pow_sup_pow_le_natCard_eisensteinPrimaryTorsionBar_quotient_mul_pow
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p)
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q) :
    ∃ C : ℕ, ∀ m M₁ : ℕ, ∃ M : ℕ, M₁ ≤ M ∧
      ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
        (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ) →
      ∀ W : AddSubgroup (JZero p),
        W ≤ eisensteinPrimaryTorsionBar p q m →
        MultiplicativeTypeNat (Aq.inertiaSubgroupIn ℚ) n W →
        (∀ σ ∈ Aq.inertiaSubgroupIn ℚ, ∀ x ∈ eisensteinPrimaryTorsionBar p q m,
          σ • (x : JZero p) - x ∈ W) →
        Nat.card (↥(heckeLatticeAlgebra p ∅) ⧸
            (Ideal.span {((q : ℕ) ^ m : ↥(heckeLatticeAlgebra p ∅))} ⊔
              (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
                (eisensteinMaximalIdeal p q)) ^ M)) ≤
          Nat.card (↥(eisensteinPrimaryTorsionBar p q m) ⧸
            W.addSubgroupOf (eisensteinPrimaryTorsionBar p q m)) * q ^ C := by sorry
