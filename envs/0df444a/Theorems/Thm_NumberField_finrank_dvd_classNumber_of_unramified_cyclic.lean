-- Prove2me | Theorems.Thm_NumberField_finrank_dvd_classNumber_of_unramified_cyclic
-- name    : NumberField.finrank_dvd_classNumber_of_unramified_cyclic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:54.185253+00:00
-- url     : https://prove2.me/theorems/0499365d-c0fe-4cc2-818c-a43905f9207b
-- title:
--   The degree of an everywhere-unramified cyclic extension divides the class number
-- statement:
--   Let $L/K$ be a finite cyclic Galois extension of number fields. Assume the inertia group is trivial at every finite prime of $K$ and every infinite place of $K$ is unramified in $L$. Then $$[L:K]\mid h_K.$$ This is the class-field-theoretic divisibility used to exclude cyclic extensions of degree $71$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Theorems.Thm_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand
open NumberField

theorem NumberField.finrank_dvd_classNumber_of_unramified_cyclic
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hfinite : ∀ v : HeightOneSpectrum (𝓞 K),
      (LanglandsTunnell.P2.Artin.primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥)
    (hinfinite : ∀ w : InfinitePlace K, w.IsUnramifiedIn L) :
    Module.finrank K L ∣ classNumber K := by sorry
