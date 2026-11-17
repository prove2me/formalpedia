-- Prove2me | Theorems.Thm_NumberField_unramified_character_eq_one_of_classNumber_le_seven
-- name    : NumberField.unramified_character_eq_one_of_classNumber_le_seven
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:54:09.589659+00:00
-- url     : https://prove2.me/theorems/e9ad7317-c5f9-4a1c-a506-da8948021757
-- title:
--   Every finite-level everywhere-unramified $ℤ/71ℤ$-character is trivial
-- statement:
--   Let $K$ be a number field with $\overline{ℚ}/K$ Galois, and let $f:\operatorname{Gal}(\overline{ℚ}/K)→ℤ/71ℤ$ be a homomorphism, with the target written multiplicatively. Assume there is a finite extension $E/K$ whose fixing subgroup lies in $\ker f$, assume $f$ is trivial on every inertia group above every rational prime, and assume $h_K≤7$. Then $$f=1.$$ This is the global vanishing input for the restricted Kummer cocycle.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq
import Theorems.Thm_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber

set_option autoImplicit false
open NumberField

theorem NumberField.unramified_character_eq_one_of_classNumber_le_seven
    (K : Type) [Field K] [NumberField K] [Algebra K (AlgebraicClosure ℚ)]
    [IsGalois K (AlgebraicClosure ℚ)]
    (f : (AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ) →* Multiplicative (ZMod 71))
    (hlevel : ∃ E : IntermediateField K (AlgebraicClosure ℚ),
      FiniteDimensional K E ∧ E.fixingSubgroup ≤ f.ker)
    (hur : ∀ (q : ℕ), q.Prime → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime q → ∀
      (σ : AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ),
      σ ∈ A.inertiaSubgroupIn K → f σ = 1)
    (hclass : classNumber K ≤ 7) : f = 1 := by sorry
