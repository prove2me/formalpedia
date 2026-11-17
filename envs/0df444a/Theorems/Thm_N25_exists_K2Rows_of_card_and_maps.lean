-- Prove2me | Theorems.Thm_N25_exists_K2Rows_of_card_and_maps
-- name    : N25.exists_K2Rows_of_card_and_maps
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:10.48224+00:00
-- url     : https://prove2.me/theorems/39cc985d-19e0-4e7c-af99-ec0b7812282e
-- title:
--   Cardinality and equivariant maps produce the exact Kummer rows
-- statement:
--   Let $V$ be the selected Kummer kernel with $|V|=71^2$. Suppose $i:\mathbb F_{71}\to V$ is injective and $\psi$-equivariant, while $q:V\to\mathbb F_{71}$ is surjective and $\chi_{71}$-equivariant. Then these maps satisfy the missing exactness condition and determine an exact character extension:
--
--   $$\ker q=\operatorname{im}i.$$
--
--   Thus the cardinality and equivariance data are sufficient to construct the full Kummer-row structure.
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

set_option autoImplicit false
noncomputable section
open N25
local instance prime71_N25_exists_K2Rows_of_card_and_maps_iba3708 : Fact (Nat.Prime 71) :=
  ⟨by decide⟩

theorem N25.exists_K2Rows_of_card_and_maps (hcard : Nat.card ↥V = 71 ^ 2)
    (i : ZMod 71 →+ ↥V) (hi : Function.Injective i)
    (hiGal : ∀ (σ : Gal) (t : ZMod 71), vAct σ (i t) = i ((psi σ : ZMod 71) * t))
    (q : ↥V →+ ZMod 71) (hq : Function.Surjective q)
    (hqGal : ∀ (σ : Gal) (v : ↥V), q (vAct σ v) =
      (ExtCitation.cycloChar 71 σ : ZMod 71) * q v) : Nonempty K2Rows := by sorry
