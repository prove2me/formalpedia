-- Prove2me | Theorems.Thm_ModularCurve_inertia_smul_smul_eq_nsmul_of_latticeRestrict_heckeEvalForms_mem_span_sup
-- name    : ModularCurve.inertia_smul_smul_eq_nsmul_of_latticeRestrict_heckeEvalForms_mem_span_sup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/183eeb41-ee59-5859-b8d5-d6f07e729de0
-- title:
--   Inertia acts by the cyclotomic character on t· v in the Eisenstein torsion tower
-- statement:
--   Let $p$ and $q$ be primes with $q\neq p$, and let $A_q$ be a valuation subring of $\overline{\mathbf{Q}}=$ `AlgebraicClosure ℚ` with $q$ a non-unit of $A_q$ (the predicate `LiesOverPrime`). Equip $J_0(p)=$ `JZero p`, the degree-zero divisor class group of the level-$p$ modular function field over $\overline{\mathbf{Q}}$, with the module structure `heckeModuleBar p` over `HeckeAlg` $=\mathbf{Z}[X_\ell:\ell\text{ prime}]$. Write $\mathfrak m=$ `eisensteinMaximalIdeal p q`, the preimage under `eisensteinEval p` of $(q)\subseteq\mathbf{Z}$, and $\varphi$ for the ring homomorphism `heckeEvalForms p 2` (sending the variable at $\ell$ to $U_\ell$ or $T_\ell$ in `heckeAlgebra p 2 ∅` according as $\ell\mid p$ or not) followed by `latticeRestrictHom p ∅`, the corestriction to its image `heckeLatticeAlgebra p ∅` of the action of that Hecke algebra on the integral lattice `intLattice p 2` of weight-$2$ cusp forms. Then for all naturals $k,M$ and every function $n$ on the group of $\mathbf{Q}$-algebra automorphisms of $\overline{\mathbf{Q}}$ such that $\sigma\zeta=\zeta^{n(\sigma)}$ for every $\sigma$ and every $\zeta$ with $\zeta^{q^k}=1$, assuming the two stability hypotheses that the submodule of $J_0(p)$ annihilated by $(q^k)+\mathfrak m^{M+1}$ coincides with that annihilated by $(q^k)+\mathfrak m^{M}$, and that $(q^k)+(\varphi_*\mathfrak m)^{M+1}=(q^k)+(\varphi_*\mathfrak m)^{M}$ in `heckeLatticeAlgebra p ∅`, the following holds: for every $t\in$ `HeckeAlg` with $\varphi(t)\in (q^k)+(\varphi_*\mathfrak m)^{M}$, every $v\in J_0(p)$ annihilated by every element of $(q^k)+\mathfrak m^{M}$, and every $\sigma$ in the inertia subgroup of $A_q$ over $\mathbf{Q}$ (the image of `inertiaSubgroup` inside the automorphism group via the decomposition subgroup), one has $\sigma\cdot(t\cdot v)=n(\sigma)\,(t\cdot v)$.
--
--   This is the elementary half of the comparison, in Mazur's study of the Eisenstein ideal, between the Hecke action on the Jacobian $J_0(p)$ and the action on the integral lattice of weight-$2$ cusp forms: Hecke elements whose lattice realisation lies in the stable ideal move the Eisenstein $(q^k,\mathfrak m^M)$-torsion into a part on which inertia at $q$ acts through the cyclotomic character mod $q^k$. It feeds the construction of the inertia-equivariant character and of the pairing on Eisenstein torsion used further downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_inertia_smul_smul_eq_nsmul_of_latticeRestrict_heckeEvalForms_mem_span_sup.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CuspForm

theorem ModularCurve.inertia_smul_smul_eq_nsmul_of_latticeRestrict_heckeEvalForms_mem_span_sup
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (_hAq : Aq.LiesOverPrime q) :
    letI := heckeModuleBar p
    ∀ k M : ℕ, ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
      (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ k) = 1 → σ ζ = ζ ^ n σ) →
      heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ (M + 1)) =
        heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M) →
      (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
          (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
            (eisensteinMaximalIdeal p q)) ^ (M + 1)) =
        (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
          (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
            (eisensteinMaximalIdeal p q)) ^ M) →
    ∀ t : HeckeAlg,
      ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) t ∈
        (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
          (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
            (eisensteinMaximalIdeal p q)) ^ M) →
      ∀ v ∈ heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
        ∀ σ ∈ Aq.inertiaSubgroupIn ℚ, σ • t • v = n σ • (t • v) := by sorry
