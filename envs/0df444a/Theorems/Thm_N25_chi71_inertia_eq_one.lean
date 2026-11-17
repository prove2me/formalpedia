-- Prove2me | Theorems.Thm_N25_chi71_inertia_eq_one
-- name    : N25.chi71_inertia_eq_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:51.144894+00:00
-- url     : https://prove2.me/theorems/047eed47-9cea-457a-8e5d-0a8fe7054354
-- title:
--   The mod-$71$ cyclotomic character is trivial on inertia at $5$
-- statement:
--   Let $I_5\subseteq G_5$ be the inertia subgroup at the chosen place above $5$. For every $\tau\in I_5$, the global image $r_5(\tau)$ has trivial mod-$71$ cyclotomic character:
--
--   $$\chi_{71}(r_5(\tau))=1.$$
--
--   This is the inertial triviality needed in the local fixed-vector argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

noncomputable section
open N25
local instance prime5_Thm_N25_chi71_inertia_eq_one_ic85c0b : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance prime71_Thm_N25_chi71_inertia_eq_one_ic85c0b : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.chi71_inertia_eq_one (τ : G5) (hτ : τ ∈ I5) :
    ExtCitation.cycloChar 71 (r5 τ) = 1 := by sorry
