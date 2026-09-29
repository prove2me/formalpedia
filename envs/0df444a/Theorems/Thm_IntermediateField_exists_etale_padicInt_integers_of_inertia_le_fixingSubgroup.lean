-- Prove2me | Theorems.Thm_IntermediateField_exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup
-- name    : IntermediateField.exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/c249212d-5164-5f78-ab0f-b7ff12dceef2
-- title:
--   An unramified étale ℤₚ-level for a finite unramified K
-- statement:
--   Let $p$ be a prime, let $\overline{\mathbb{Q}}_p$ denote the chosen algebraic closure of $\mathbb{Q}_p$, and let $\mathcal{O}$ be the valuation subring of $\overline{\mathbb{Q}}_p$ attached to its canonical $\mathbb{R}_{\ge 0}$-valued valuation. Let $K$ be an intermediate field of $\overline{\mathbb{Q}}_p/\mathbb{Q}_p$ which is finite-dimensional over $\mathbb{Q}_p$, and assume that the inertia subgroup of $\mathcal{O}$ over $\mathbb{Q}_p$ — that is, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ of the inertia subgroup of $\mathcal{O}$ sitting inside its decomposition subgroup — is contained in the subgroup of $\mathbb{Q}_p$-automorphisms of $\overline{\mathbb{Q}}_p$ fixing $K$ pointwise. The assertion is that there exists a type $B$, equipped with the structure of a commutative ring which is a domain, a $\mathbb{Z}_p$-algebra structure making $B$ a finite free $\mathbb{Z}_p$-module and étale over $\mathbb{Z}_p$, and a $B$-algebra structure on $\overline{\mathbb{Q}}_p$ compatible with the maps from $\mathbb{Z}_p$, such that: (i) every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ fixing the image of $B$ in $\overline{\mathbb{Q}}_p$ pointwise fixes $K$ pointwise; and (ii) every $x \in K$ whose valuation, in the value group of $\mathcal{O}$, equals $1$ is the image of a unit of $B$.
--
--   The statement produces an integral "étale level" over $\mathbb{Z}_p$ adapted to a finite unramified extension $K$ of $\mathbb{Q}_p$: concretely, a finite free étale $\mathbb{Z}_p$-algebra embedded in $\overline{\mathbb{Q}}_p$ which cuts out a field containing $K$ and already contains all valuation-one elements of $K$ as units. It is used in the construction of [`HopfAlgebra.exists_hopf_points_subquotient_of_unitKummer_over_etale_level`](thm.html#HopfAlgebra.exists_hopf_points_subquotient_of_unitKummer_over_etale_level), and rests on the identification of the inertia subgroup as the fixing subgroup of the prime-to-$p$ roots of unity and on the characterisation of $\mathbb{Z}_p$-integrality in $\overline{\mathbb{Q}}_p$ by $\|x\| \le 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) (hK : FiniteDimensional ℚ_[p] K)
    (hKur : (padicIntegers p).inertiaSubgroupIn ℚ_[p] ≤ K.fixingSubgroup) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra ℤ_[p] B) (_ : Module.Finite ℤ_[p] B)
      (_ : Module.Free ℤ_[p] B) (_ : Algebra.Etale ℤ_[p] B)
      (_ : Algebra B (AlgebraicClosure ℚ_[p])) (_ : IsScalarTower ℤ_[p] B (AlgebraicClosure ℚ_[p])),
      (∀ σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) = algebraMap B (AlgebraicClosure ℚ_[p]) b) →
          σ ∈ K.fixingSubgroup) ∧
      (∀ x : AlgebraicClosure ℚ_[p], x ∈ K → (padicIntegers p).valuation x = 1 →
        ∃ b : B, IsUnit b ∧ algebraMap B (AlgebraicClosure ℚ_[p]) b = x) := by sorry
