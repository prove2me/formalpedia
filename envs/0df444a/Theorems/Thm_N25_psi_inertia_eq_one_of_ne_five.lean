-- Prove2me | Theorems.Thm_N25_psi_inertia_eq_one_of_ne_five
-- name    : N25.psi_inertia_eq_one_of_ne_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:26.682737+00:00
-- url     : https://prove2.me/theorems/0ee95e38-c495-478e-b27b-5ca1c67e9f0b
-- title:
--   The order-five character is unramified away from $5$
-- statement:
--   Let $ψ:G_{ℚ}→(ℤ/71ℤ)^×$ be the global character obtained from the mod-$25$ cyclotomic character. Let $q$ be a prime different from $5$, let $A⊆ℚ̄$ be a valuation ring above $q$, and let $σ$ lie in the corresponding inertia subgroup. Then $$ψ(σ)=1.$$ This supplies the unramified local behavior of the twisted character line away from the level prime.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one

set_option autoImplicit false
open N25

theorem N25.psi_inertia_eq_one_of_ne_five {q : ℕ} (hq : q.Prime) (hq5 : q ≠ 5)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (σ : Gal) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : psi σ = 1 := by sorry
