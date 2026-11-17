-- Prove2me | Theorems.Thm_N25_K2Rows_local_coboundary_lift_at_five
-- name    : N25.K2Rows.local_coboundary_lift_at_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:58.304624+00:00
-- url     : https://prove2.me/theorems/addefe31-6090-47b3-a443-23d96be2a142
-- title:
--   A local coboundary in the kernel comes from the $ψ$-line
-- statement:
--   Let $G_5=\mathrm{Gal}(ℚ̄_5/ℚ_5)$, let $r_5:G_5\to G_{ℚ}$ be the chosen restriction map, and assume the frozen exact filtration with inclusion $i:𝔽_{71}(ψ)\to V$. Suppose $c:G_5\to 𝔽_{71}$ and $b\in V$ satisfy $i(c(τ))=r_5(τ)b-b$ for every $τ\in G_5$. Then there exists $a\in 𝔽_{71}$ such that $$c(τ)=ψ(r_5(τ))a-a\quad\text{for every }τ\in G_5.$$ This extracts the one-dimensional local coboundary needed at the prime $5$.
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
local instance fact_prime_seventyOne_K2Rows_lift_i6ee148 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.K2Rows.local_coboundary_lift_at_five
    (hK2 : K2Rows) (c : G5 → ZMod 71) (b : ↥V)
    (hc : ∀ τ, hK2.i (c τ) = vAct (r5 τ) b - b) :
    ∃ a : ZMod 71, ∀ τ, c τ = (psi (r5 τ) : ZMod 71) * a - a := by sorry
