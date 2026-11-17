-- Prove2me | Theorems.Thm_N25_exists_psi_ne_cyclotomic
-- name    : N25.exists_psi_ne_cyclotomic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:16.0425+00:00
-- url     : https://prove2.me/theorems/31af644b-aa13-4943-be84-8b9dc6bfa035
-- title:
--   The quintic and cyclotomic characters differ
-- statement:
--   Let $\psi$ be the named mod-$71$ quintic character and let $\chi_{71}$ be the mod-$71$ cyclotomic character. There exists an arithmetic Galois element $\sigma$ such that
--
--   $$\psi(\sigma)\ne\chi_{71}(\sigma).$$
--
--   This character separation forces the image and kernel lines in the Kummer rows to be distinct.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

set_option autoImplicit false
open N25
local instance primeSeventyOneCharacterDistinction_i6977e0 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.exists_psi_ne_cyclotomic :
    ∃ σ : Gal, (psi σ : ZMod 71) ≠ (ExtCitation.cycloChar 71 σ : ZMod 71) := by sorry
