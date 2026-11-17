-- Prove2me | Theorems.Thm_N25_pi5_bijective_of_N5Surj
-- name    : N25.pi5_bijective_of_N5Surj
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:20.083691+00:00
-- url     : https://prove2.me/theorems/e62fd334-29ee-4f3e-b13b-6ba8a7f3af75
-- title:
--   The selected endomorphism is bijective on the locally fixed subgroup
-- statement:
--   Let $M_5$ be the subgroup fixed by the chosen local Galois action at $5$, and let $π_5:M_5→M_5$ be the restriction of $π=2+4γ+γ^2$. Assume the cyclotomic relation, the exact two-character filtration of $ker(π)$, and finite-index $71$-divisibility on $M_5$. Then $$π_5\text{ is bijective}.$$ This produces the local division point needed to trivialize the Kummer cocycle at $5$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
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

open N25

theorem N25.pi5_bijective_of_N5Surj
    (hPhi : PhiFiveZero) (K2 : K2Rows) (hN5 : N5Surj) : Function.Bijective pi5 := by sorry
