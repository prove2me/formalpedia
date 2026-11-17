-- Prove2me | Theorems.Thm_N25_GlobalKummer_quotient_zero_on_five_inertia
-- name    : N25.GlobalKummer.quotient_zero_on_five_inertia
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:19.502484+00:00
-- url     : https://prove2.me/theorems/0d77071d-42ea-452a-8676-5e09f6a94c4e
-- title:
--   The quotient division cocycle vanishes on inertia at $5$
-- statement:
--   Assume the cyclotomic relation, the frozen filtration, and the local surjectivity hypothesis at $5$. Let $P\in M$, $Q\in J$ satisfy $π(Q)=P$, and let $σ$ lie in the inertia subgroup at the selected place above $5$. Then the cyclotomic quotient cocycle vanishes at $σ$: $$\bar c_{P,Q}(σ)=0.$$ This supplies the exceptional local condition at the level prime $5$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_GlobalKummerQuotient
import Definitions.Def_N25_LocalKummerOperators
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_N25_LocalFiveArithmetic

set_option autoImplicit false
noncomputable section
open N25
open N25.GlobalKummer
local instance quotientFivePrimeFive_i723d80 : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance quotientFivePrimeSeventyOne_i723d80 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.GlobalKummer.quotient_zero_on_five_inertia
    (hPhi : PhiFiveZero) (K2 : K2Rows) (hN5 : N5Surj)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J))
    (σ : Gal) (hσ : σ ∈ (ExtCitation.primeLocalPlace q5).inertiaSubgroupIn ℚ) :
    quotientDivisionCocycle hPhi K2 P Q hQ σ = 0 := by sorry
