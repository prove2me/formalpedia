-- Prove2me | Theorems.Thm_N25_kummer_at_five_is_coboundary_of_N5Surj
-- name    : N25.kummer_at_five_is_coboundary_of_N5Surj
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:48.389175+00:00
-- url     : https://prove2.me/theorems/fdc64dd2-6722-4004-b3a0-364d616a4324
-- title:
--   Local $71$-division at $5$ makes the Kummer cocycle a coboundary
-- statement:
--   Let $π=2+4γ+γ^2$, let $V=ker(π)$, and let $G_5$ be the selected local Galois group with map $r_5:G_5→G_{ℚ}$. Assume the cyclotomic relation, the frozen exact filtration of $V$, and a finite-index subgroup of the locally fixed group on which multiplication by $71$ is surjective. If $P∈J$ is globally fixed and $π(Q)=P$, then there exists $v∈V$ such that $$r_5(τ)Q-Q=r_5(τ)v-v\qquad\text{for every }τ∈G_5.$$ This supplies the coboundary condition at the exceptional prime $5$.
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

theorem N25.kummer_at_five_is_coboundary_of_N5Surj
    (hPhi : PhiFiveZero) (K2 : K2Rows) (hN5 : N5Surj)
    (P Q : J) (hP : P ∈ M) (hQ : piEnd Q = P) :
    ∃ v : ↥V, ∀ τ : G5, r5 τ • Q - Q = r5 τ • (v : J) - (v : J) := by sorry
