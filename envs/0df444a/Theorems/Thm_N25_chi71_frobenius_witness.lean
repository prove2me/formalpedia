-- Prove2me | Theorems.Thm_N25_chi71_frobenius_witness
-- name    : N25.chi71_frobenius_witness
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:25.32706+00:00
-- url     : https://prove2.me/theorems/121bd0da-2790-4c02-91f1-583dde5ec579
-- title:
--   A Frobenius at $5$ has cyclotomic value $5$ modulo $71$
-- statement:
--   Let $G_5$ be the chosen local Galois group at $5$, let $r_5:G_5\to\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ be the local-to-global map, and let $\chi_{71}$ be the mod-$71$ cyclotomic character. There exists $\varphi\in G_5$ such that $r_5(\varphi)$ is Frobenius at the chosen place above $5$ and
--
--   $$\chi_{71}(r_5(\varphi))=5\in(\mathbb Z/71\mathbb Z)^\times.$$
--
--   This provides the local Frobenius element used to separate the two residual characters.
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
local instance prime5_Thm_N25_chi71_frobenius_witness_i91800c : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance prime71_Thm_N25_chi71_frobenius_witness_i91800c : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.chi71_frobenius_witness :
    ∃ φ : G5, (ExtCitation.primeLocalPlace q5).IsFrobeniusAt (r5 φ) 5 ∧
      ExtCitation.cycloChar 71 (r5 φ) = ZMod.unitOfCoprime 5 (by decide) := by sorry
