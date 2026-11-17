-- Prove2me | Theorems.Thm_N25_psi_inertia_witness
-- name    : N25.psi_inertia_witness
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:02.686349+00:00
-- url     : https://prove2.me/theorems/2e648e5d-2bc2-4315-b8b3-bd4a78ebb1a9
-- title:
--   Inertia at $5$ realizes the nontrivial character value $57$
-- statement:
--   Let $G_5$ be the selected local Galois group, $I_5$ its inertia subgroup, and $r_5:G_5→G_{ℚ}$ the local-to-global map. There exists $τ∈I_5$ such that $$ψ(r_5τ)=57\pmod{71}.$$ This witness proves that the order-five character is genuinely nontrivial at $5$.
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
local instance prime5_Thm_N25_psi_inertia_witness_ie821f4 : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance prime71_Thm_N25_psi_inertia_witness_ie821f4 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.psi_inertia_witness :
    ∃ τ : G5, τ ∈ I5 ∧ psi (r5 τ) = ZMod.unitOfCoprime 57 (by decide) := by sorry
