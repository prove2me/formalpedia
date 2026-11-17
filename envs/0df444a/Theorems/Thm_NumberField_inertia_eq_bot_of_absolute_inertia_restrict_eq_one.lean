-- Prove2me | Theorems.Thm_NumberField_inertia_eq_bot_of_absolute_inertia_restrict_eq_one
-- name    : NumberField.inertia_eq_bot_of_absolute_inertia_restrict_eq_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:51.13632+00:00
-- url     : https://prove2.me/theorems/d30f5056-09ab-4290-8723-02e6315abbb4
-- title:
--   Trivial restriction of absolute inertia forces relative finite-prime inertia to vanish
-- statement:
--   Let $K$ be a number field embedded in $\overline{ℚ}$ with $\overline{ℚ}/K$ Galois, and let $M/K$ be a normal intermediate number field. Assume that for every rational prime $q$, every valuation ring $A$ of $\overline{ℚ}$ above $q$, and every $σ$ in the inertia group of $A/K$, the restriction of $σ$ to $M$ is the identity. Then for every height-one prime $w$ of $\mathcal O_M$, $$I_w(M/K)=\{1\}.$$ This transfers an absolute inertia condition to ordinary relative ramification.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq

set_option autoImplicit false
open IsDedekindDomain
open NumberField

theorem NumberField.inertia_eq_bot_of_absolute_inertia_restrict_eq_one
    (K : Type) [Field K] [NumberField K] [Algebra K (AlgebraicClosure ℚ)]
    [IsGalois K (AlgebraicClosure ℚ)]
    (M : IntermediateField K (AlgebraicClosure ℚ))
    [NumberField M] [Normal K M]
    (hur : ∀ (q : ℕ), q.Prime → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime q → ∀
      (σ : AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ),
      σ ∈ A.inertiaSubgroupIn K → σ.restrictNormal M = 1)
    (w : HeightOneSpectrum (𝓞 M)) :
    w.asIdeal.inertia (M ≃ₐ[K] M) = ⊥ := by sorry
