-- Prove2me | Theorems.Thm_ModularCurve_exists_submodule_multiplicativeTypeNat_heckeTorsion_span_sup_pairing_heckeLatticeAlgebra_quotient_of_ne_two
-- name    : ModularCurve.exists_submodule_multiplicativeTypeNat_heckeTorsion_span_sup_pairing_heckeLatticeAlgebra_quotient_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/44a9c3a2-2f39-566d-96ec-433a899ab7e5
-- title:
--   Multiplicative-type submodule and pairing of Eisenstein torsion (q ≠ 2)
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$ and $q \neq p$, and let $A_q$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A_q$. Write $\mathbb{T} = \mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbb{Z}$ for the abstract Hecke polynomial ring, let $J_0(p)$ denote the degree-zero divisor class group of the modular function field of level $p$ over $\overline{\mathbb{Q}}$ with its $\mathbb{T}$-module structure given by `heckeModuleBar`, and let $\mathfrak{P} =$ `eisensteinMaximalIdeal p q` be the preimage under the Eisenstein evaluation map of the ideal $(q)$ of $\mathbb{Z}$. Let $R =$ `heckeLatticeAlgebra p ∅` be the image of the weight-two Hecke algebra of level $p$ in $\mathrm{End}_{\mathbb{Z}}$ of the integral lattice of cusp forms, and let $\varphi : \mathbb{T} \to R$ be the composite of `heckeEvalForms p 2` (sending the variable at a prime $\ell$ to $U_\ell$ if $\ell \mid p$ and to $T_\ell$ otherwise) with `latticeRestrictHom`. For all natural numbers $k, M$ and every function $n$ on $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ such that $\sigma(\zeta) = \zeta^{n(\sigma)}$ for all $\sigma$ and all $\zeta$ with $\zeta^{q^k} = 1$, assume that the submodule $T_M$ of elements of $J_0(p)$ annihilated by $(q^k) + \mathfrak{P}^M$ is unchanged on replacing $M$ by $M+1$, and likewise that the ideals $(q^k) + (\varphi_* \mathfrak{P})^M$ of $R$ coincide for $M$ and $M+1$. Then there is a $\mathbb{T}$-submodule $W \leq T_M$ such that: inertia at $A_q$ (the image in the full Galois group of the inertia subgroup of the decomposition subgroup of $A_q$) acts on $W$ by $\sigma \cdot x = n(\sigma)\, x$; every displacement $\sigma x - x$ with $\sigma$ in that inertia group and $x \in T_M$ lies in $W$; and there is a function $e$ from $T_M \times \bigl(R/((q^k) + (\varphi_*\mathfrak{P})^M)\bigr)$ to $\overline{\mathbb{Q}}^{\times}$ which is multiplicative in each variable separately, satisfies $e(t \cdot v, r) = e(v, \overline{\varphi(t)}\, r)$ for $t \in \mathbb{T}$, is non-degenerate in the second variable ($e(v,r) = 1$ for all $v$ forces $r = 0$), and whose left kernel is exactly $W$ ($e(v,r) = 1$ for all $r$ if and only if $v \in W$).
--
--   This is the form, at principal level $p$, of Mazur's description of the multiplicative-type part of the $q$-power Eisenstein torsion of $J_0(p)$ together with the duality between the quotient by that part and the corresponding quotient of the Hecke algebra acting on the integral weight-two lattice. It is used in the counting step bounding the order of the quotient of the lattice Hecke algebra by $(q^k) + (\varphi_*\mathfrak{P})^M$ in terms of the order of the Eisenstein-primary torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_submodule_multiplicativeTypeNat_heckeTorsion_span_sup_pairing_heckeLatticeAlgebra_quotient_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_ModularCurve_MultiplicativeType
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CuspForm

theorem ModularCurve.exists_submodule_multiplicativeTypeNat_heckeTorsion_span_sup_pairing_heckeLatticeAlgebra_quotient_of_ne_two
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
    ∃ W : Submodule HeckeAlg (JZero p),
      W ≤ heckeTorsion (JZero p)
        (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M) ∧
      MultiplicativeTypeNat (Aq.inertiaSubgroupIn ℚ) n W.toAddSubgroup ∧
      (∀ σ ∈ Aq.inertiaSubgroupIn ℚ,
        ∀ x ∈ heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
        σ • (x : JZero p) - x ∈ W) ∧
      ∃ e : ↥(heckeTorsion (JZero p)
              (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M)) →
            (↥(heckeLatticeAlgebra p ∅) ⧸
              (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
                (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
                  (eisensteinMaximalIdeal p q)) ^ M)) → (AlgebraicClosure ℚ)ˣ,
        (∀ v₁ v₂ r, e (v₁ + v₂) r = e v₁ r * e v₂ r) ∧
        (∀ v r₁ r₂, e v (r₁ + r₂) = e v r₁ * e v r₂) ∧
        (∀ (t : HeckeAlg) (v) r,
          e (t • v) r =
            e v (((Ideal.Quotient.mk
                (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
                  (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
                    (eisensteinMaximalIdeal p q)) ^ M)).comp
              ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))) t * r)) ∧
        (∀ r, (∀ v, e v r = 1) → r = 0) ∧
        (∀ v, (∀ r, e v r = 1) ↔ (v : JZero p) ∈ W) := by sorry
