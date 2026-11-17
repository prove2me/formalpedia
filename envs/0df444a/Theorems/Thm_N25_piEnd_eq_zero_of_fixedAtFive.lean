-- Prove2me | Theorems.Thm_N25_piEnd_eq_zero_of_fixedAtFive
-- name    : N25.piEnd_eq_zero_of_fixedAtFive
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:21.134523+00:00
-- url     : https://prove2.me/theorems/98142f4d-5667-43b2-b790-993b2fb51c8e
-- title:
--   No nonzero kernel point is fixed at $5$
-- statement:
--   Let $V=ker(π)$ and assume its frozen exact two-character filtration. If $x∈J$ satisfies $π(x)=0$ and is fixed by every element of the chosen local Galois group at $5$, then $$x=0.$$ This is the local fixed-point vanishing that makes the restricted endomorphism injective.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

noncomputable section
open N25
local instance prime71_Thm_N25_piEnd_eq_zero_of_fixedAtFive_ie93ae7 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.piEnd_eq_zero_of_fixedAtFive (K2 : K2Rows) (x : J)
    (hπ : piEnd x = 0) (hfixed : ∀ τ : G5, r5 τ • x = x) : x = 0 := by sorry
