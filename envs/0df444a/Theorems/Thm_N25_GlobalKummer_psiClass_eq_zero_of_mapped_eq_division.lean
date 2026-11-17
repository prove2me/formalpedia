-- Prove2me | Theorems.Thm_N25_GlobalKummer_psiClass_eq_zero_of_mapped_eq_division
-- name    : N25.GlobalKummer.psiClass_eq_zero_of_mapped_eq_division
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:08:10.279507+00:00
-- url     : https://prove2.me/theorems/981603c9-127c-4a75-b88f-d92567bf449d
-- title:
--   Any $ψ$-lift of the division class is zero
-- statement:
--   Assume the cyclotomic relation, the frozen filtration, and the ordinary finite-flat condition at $71$. Let $P\in M$, $Q\in J$ satisfy $π(Q)=P$, and let $z\in H^1_S(G_{ℚ},𝔽_{71}(ψ))$, where $S=\{5,71\}$. If its image under $i_*$ equals the division class, then $$i_*[z]=[c_{P,Q}]\quad\Longrightarrow\quad [z]=0\ \text{in }H^1(G_{ℚ},𝔽_{71}(ψ)).$$ This kills the remaining one-dimensional obstruction after the cyclotomic quotient has vanished.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic
import Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq
import Theorems.Thm_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber
import Theorems.Thm_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_N25_LocalFiniteFlatClasses
import Definitions.Def_N25_OrdinaryKummerFiniteFlat
import Definitions.Def_N25_LocalKummerOperators
import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalFiveArithmetic
import Definitions.Def_N25_LocalFiveCondition
import Definitions.Def_N25_RatPointModel
import Definitions.Def_N25_LocalCarrier
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
import Definitions.Def_N25_LocalFiveIntegralPoints
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
import Theorems.Thm_HopfAlgebra_act_eq_self_of_inertiaTrivialChain_padicInt
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff
import Definitions.Def_GaloisRep_CompletionBridge

set_option autoImplicit false
noncomputable section
open CategoryTheory groupCohomology
open scoped Pointwise
open N25
open N25.GlobalKummer
local instance psiMappedPrimeSeventyOne_id9d3f7 : Fact (Nat.Prime 71) := ⟨by decide⟩
local instance psiMappedPrimeFive_id9d3f7 : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem N25.GlobalKummer.psiClass_eq_zero_of_mapped_eq_division
    (hPhi : PhiFiveZero) (K2 : K2Rows) (hN71 : OrdinaryKummerFiniteFlat)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J))
    (z : ↥(continuousH1S ramificationSet psiRep))
    (hmap : (groupCohomology.map (MonoidHom.id Gal) (kernelInclusion hPhi K2) 1).hom
      (z : H1 psiRep) = H1π (vRep hPhi) (divisionCocycle hPhi P Q hQ)) :
    (z : H1 psiRep) = 0 := by sorry
