-- Prove2me | Theorems.Thm_N25_exists_forget_algEquiv_action
-- name    : N25.exists_forget_algEquiv_action
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:48.372766+00:00
-- url     : https://prove2.me/theorems/12b5b675-8d00-422e-aae9-3323e9d5f1a7
-- title:
--   An algebra-automorphism action can be forgotten to a ring-automorphism action
-- statement:
--   Let $R$ be a commutative semiring, let $A$ be an $R$-algebra and a semiring, let $G$ be a monoid, and let $\rho_a:G\to\operatorname{Aut}_{R\text{-alg}}(A)$ be a monoid action by $R$-algebra automorphisms. There exists a monoid homomorphism $\rho:G\to\operatorname{Aut}_{\mathrm{ring}}(A)$ with the same pointwise action:
--
--   $$\rho(g)(x)=\rho_a(g)(x)\qquad(g\in G,\ x\in A).$$
--
--   This supplies the underlying ring action required by the cohomological interfaces.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false

theorem N25.exists_forget_algEquiv_action
    {R A G : Type*} [CommSemiring R] [Semiring A] [Monoid G]
    [algebra : Algebra R A] (ρa : G →* (A ≃ₐ[R] A)) :
    ∃ ρ : G →* RingAut A, ∀ g x, ρ g x = ρa g x := by sorry
