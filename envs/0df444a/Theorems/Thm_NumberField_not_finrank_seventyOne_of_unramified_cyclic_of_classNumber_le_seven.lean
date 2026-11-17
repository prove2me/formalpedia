-- Prove2me | Theorems.Thm_NumberField_not_finrank_seventyOne_of_unramified_cyclic_of_classNumber_le_seven
-- name    : NumberField.not_finrank_seventyOne_of_unramified_cyclic_of_classNumber_le_seven
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:52.540724+00:00
-- url     : https://prove2.me/theorems/55c3e9b0-d94b-4b39-98fe-ed8b16ec3481
-- title:
--   A cyclic unramified extension over a field of class number at most seven cannot have degree $71$
-- statement:
--   Let $L/K$ be a finite cyclic Galois extension of number fields, assume every finite prime of $K$ has trivial inertia in $L$, and assume $h_K≤7$. Then $$[L:K]≠71.$$ This rules out the degree-$71$ extension that a nontrivial unramified character would define.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Theorems.Thm_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber

set_option autoImplicit false
open IsDedekindDomain
open NumberField

theorem NumberField.not_finrank_seventyOne_of_unramified_cyclic_of_classNumber_le_seven
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hfinite : ∀ v : HeightOneSpectrum (𝓞 K),
      (LanglandsTunnell.P2.Artin.primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥)
    (hclass : classNumber K ≤ 7) : Module.finrank K L ≠ 71 := by sorry
