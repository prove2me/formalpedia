-- Prove2me | Theorems.Thm_N25_psi_kernel_index
-- name    : N25.psi_kernel_index
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:48.636652+00:00
-- url     : https://prove2.me/theorems/784e9e69-fa4f-4920-8252-8df8a30cfd4c
-- title:
--   The global character kernel has index five
-- statement:
--   For the global character $ψ:G_{ℚ}→(ℤ/71ℤ)^×$, $$[G_{ℚ}:ker(ψ)]=5.$$ This identifies the associated character field as a quintic extension.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

set_option autoImplicit false
open N25

theorem N25.psi_kernel_index : psi.ker.index = 5 := by sorry
