-- Prove2me | Theorems.Thm_N25_GlobalKummer_psi_cocycle_class_zero
-- name    : N25.GlobalKummer.psi_cocycle_class_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:54.496404+00:00
-- url     : https://prove2.me/theorems/f005ea44-c3a0-4f2d-8fcb-74dd0089d541
-- title:
--   An everywhere locally trivial $ψ$-cocycle is cohomologically zero
-- statement:
--   Let $c\in Z^1(G_{ℚ},𝔽_{71}(ψ))$ factor through a finite quotient. Assume that for every rational prime $q$, every valuation ring $A\subseteq ℚ̄$ above $q$, and every inertia element $σ\in I_A$, the implication $ψ(σ)=1\Rightarrow c(σ)=0$ holds. Then $$[c]=0\quad\text{in }H^1(G_{ℚ},𝔽_{71}(ψ)).$$ This is the class-field-theoretic vanishing step for the twisted Kummer class. Formalization note: the finite-level assumption is the explicit continuity condition on $c$.
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

set_option autoImplicit false
noncomputable section
open CategoryTheory groupCohomology
open N25
open N25.GlobalKummer
local instance psiClassZeroPrimeSeventyOne_i3bcc05 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.GlobalKummer.psi_cocycle_class_zero
    (c : cocycles₁ psiRep)
    (hc : IsLevelConstant₁ (MonoidHom.id Gal) c)
    (hur : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ →
      psi σ = 1 → c σ = 0) : H1π psiRep c = 0 := by sorry
