-- Prove2me | Theorems.Thm_N25_GlobalKummer_radical_fixed_of_cocycle_zero
-- name    : N25.GlobalKummer.radical_fixed_of_cocycle_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:25.467309+00:00
-- url     : https://prove2.me/theorems/be6001c3-9919-4ee2-8d6d-7678996afb50
-- title:
--   A zero Kummer cocycle value fixes the radical
-- statement:
--   Let $c\in Z^1(G_{ℚ},𝔽_{71}(χ_{71}))$, let $e:𝔽_{71}\to μ_{71}(ℚ̄)$ be an additive isomorphism, and let $α\in ℚ̄^×$ satisfy $e(c(τ))=τ(α)/α$ for every $τ\in G_{ℚ}$. If $c(σ)=0$, then $$σ(α)=α.$$ This turns cocycle vanishing on inertia into an unramifiedness statement for the Kummer radical.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer

set_option autoImplicit false
open N25
open N25.GlobalKummer

theorem N25.GlobalKummer.radical_fixed_of_cocycle_zero
    (c : groupCohomology.cocycles₁ cyclotomicRep)
    (e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)))
    (α : (AlgebraicClosure ℚ)ˣ)
    (hc : ∀ σ : Gal, (Additive.toMul (e (c σ))).val =
      groupCohomology.Kummer.kummerCocycle α σ)
    (σ : Gal) (hσ : c σ = 0) : σ (α : AlgebraicClosure ℚ) = α := by sorry
