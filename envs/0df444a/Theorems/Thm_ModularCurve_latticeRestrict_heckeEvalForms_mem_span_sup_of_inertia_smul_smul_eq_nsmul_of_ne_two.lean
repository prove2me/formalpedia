-- Prove2me | Theorems.Thm_ModularCurve_latticeRestrict_heckeEvalForms_mem_span_sup_of_inertia_smul_smul_eq_nsmul_of_ne_two
-- name    : ModularCurve.latticeRestrict_heckeEvalForms_mem_span_sup_of_inertia_smul_smul_eq_nsmul_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/41e7bd5a-0650-5165-ad1c-4a2cf8b6cc81
-- title:
--   Inertia eigenvectors force membership in the stable lattice ideal
-- statement:
--   Fix primes $p$ and $q$ (as `Fact`-instances) with $q \neq 2$ and $q \neq p$, and a valuation subring $A_q$ of $\overline{\mathbf{Q}}$ lying over $q$ in the sense that the image of $q$ lies in the non-units of $A_q$. Equip $J_0(p) :=$ `JZero p`, the degree-zero divisor class group $\mathrm{Pic}^0$ of the base-changed modular function field of level $p$ over $\overline{\mathbf{Q}}$, with the `HeckeAlg`-module structure `heckeModuleBar p`, where `HeckeAlg` is the polynomial ring $\mathbf{Z}[X_\ell : \ell \text{ prime}]$. Let $k, M \in \mathbf{N}$ and let $n : \mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q}) \to \mathbf{N}$ satisfy $\sigma\zeta = \zeta^{n(\sigma)}$ for every $\sigma$ and every $\zeta \in \overline{\mathbf{Q}}$ with $\zeta^{q^k} = 1$. Write $I_{k,M}$ for the ideal $(q^k) \sqcup \mathfrak{m}^M$ of `HeckeAlg`, where $\mathfrak{m} =$ `eisensteinMaximalIdeal p q` is the preimage under `eisensteinEval p` of the ideal $(q)$ of $\mathbf{Z}$, and let $\pi$ be the composite of `heckeEvalForms p 2` (sending the variable $\ell$ to $U_\ell$ if $\ell \mid p$ and to $T_\ell$ otherwise) with `latticeRestrictHom p ∅`, valued in the subalgebra `heckeLatticeAlgebra p ∅` of $\mathbf{Z}$-endomorphisms of the integral lattice in weight-$2$ cusp forms for $\Gamma_0(p)$. Assume two stabilisation hypotheses: the torsion submodules `heckeTorsion (JZero p)` of $I_{k,M+1}$ and of $I_{k,M}$ coincide, and the ideals $(q^k) \sqcup (\mathfrak{m}\,\text{mapped by }\pi)^{M+1}$ and $(q^k) \sqcup (\mathfrak{m}\,\text{mapped by }\pi)^{M}$ of `heckeLatticeAlgebra p ∅` coincide. Then for every $t \in$ `HeckeAlg` such that $\sigma \cdot (t \cdot v) = n(\sigma) \cdot (t \cdot v)$ for all $v$ in the $I_{k,M}$-torsion of $J_0(p)$ and all $\sigma$ in the image of the inertia subgroup of $A_q$ inside $\mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$, the element $\pi(t)$ lies in $(q^k) \sqcup (\mathfrak{m}\,\text{mapped by }\pi)^{M}$.
--
--   This is the faithfulness half of the analysis of the Eisenstein torsion tower of $J_0(p)$ at an auxiliary odd prime $q \neq p$: an operator acting on the whole $(q^k, \mathfrak{m}^M)$-torsion through inertia eigenvectors at $q$ is already congruent to zero in the lattice Hecke quotient. It feeds into the construction of a pairing between the Eisenstein torsion and the quotient of the lattice Hecke algebra used for the multiplicative-type maximal ideal statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_latticeRestrict_heckeEvalForms_mem_span_sup_of_inertia_smul_smul_eq_nsmul_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CuspForm

theorem ModularCurve.latticeRestrict_heckeEvalForms_mem_span_sup_of_inertia_smul_smul_eq_nsmul_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p)
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
      (∀ v ∈ heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
        ∀ σ ∈ Aq.inertiaSubgroupIn ℚ, σ • t • v = n σ • (t • v)) →
      ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) t ∈
        (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
          (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
            (eisensteinMaximalIdeal p q)) ^ M) := by sorry
