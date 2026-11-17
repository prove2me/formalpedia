-- Prove2me | Theorems.Thm_N25_GlobalKummer_division_quotient_class_zero
-- name    : N25.GlobalKummer.division_quotient_class_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:08:15.900197+00:00
-- url     : https://prove2.me/theorems/62994e84-a6b6-4287-84ad-25ad4dae1d23
-- title:
--   The cyclotomic quotient of the division class vanishes
-- statement:
--   Assume the cyclotomic relation, the exact filtration $0\to 𝔽_{71}(ψ)\to V\to 𝔽_{71}(χ_{71})\to0$, and the ordinary finite-flat condition at $71$. If $P\in M$, $Q\in J$, and $π(Q)=P$, let $\bar c_{P,Q}$ be the image of $c_{P,Q}(σ)=σQ-Q$ in the cyclotomic quotient $𝔽_{71}(χ_{71})$. Then $$[\bar c_{P,Q}]=0\quad\text{in }H^1(G_{ℚ},𝔽_{71}(χ_{71})).$$ This removes the cyclotomic obstruction to lifting the division class into the $ψ$-line.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_GlobalKummerQuotient
import Definitions.Def_N25_GlobalKummerRamification
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level
import Definitions.Def_N25_LocalFiniteFlatClasses
import Definitions.Def_N25_LocalKummerOperators
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_N25_LocalFiveArithmetic
import Definitions.Def_N25_OrdinaryKummerFiniteFlat
import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
import Theorems.Thm_HopfAlgebra_exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
import Theorems.Thm_PadicAlgCl_exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_valuation_ratCast_eq_zpow_padicValRat
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

set_option autoImplicit false
noncomputable section
open N25
open N25.GlobalKummer
local instance quotientVanishingPrimeSeventyOne_idb5021 : Fact (Nat.Prime 71) := ⟨by decide⟩
local instance quotientVanishingPrimeFive_idb5021 : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem N25.GlobalKummer.division_quotient_class_zero
    (hPhi : PhiFiveZero) (K2 : K2Rows) (hN71 : OrdinaryKummerFiniteFlat)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J)) :
    groupCohomology.H1π cyclotomicRep (quotientDivisionCocycle hPhi K2 P Q hQ) = 0 := by sorry
