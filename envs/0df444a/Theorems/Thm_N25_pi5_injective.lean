-- Prove2me | Theorems.Thm_N25_pi5_injective
-- name    : N25.pi5_injective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:48.376786+00:00
-- url     : https://prove2.me/theorems/d5359b8c-674a-4e7e-88b1-abcff574e424
-- title:
--   The selected endomorphism is injective on the locally fixed subgroup
-- statement:
--   Let $M_5$ be the subgroup fixed by the chosen local Galois action at $5$, let $π_5$ be the restriction of $π=2+4γ+γ^2$, and assume the frozen exact filtration of $V=ker(π)$. Then $$ker(π_5)=0.$$ This rules out locally fixed nonzero kernel points and is the injective half of local bijectivity.
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

theorem N25.pi5_injective (K2 : K2Rows) : Function.Injective pi5 := by sorry
