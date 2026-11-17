-- Prove2me | Theorems.Thm_N25_Endgame_frobenius_pushforward_single_of_deg_one
-- name    : N25.Endgame.frobenius_pushforward_single_of_deg_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:23:38.86442+00:00
-- url     : https://prove2.me/theorems/40fe2942-3ff4-47d0-a6e3-2d07fbb97c6b
-- title:
--   Frobenius pushforward sends a degree-one point divisor to its Frobenius image
-- statement:
--   Let $K$ be a perfect field of characteristic $ℓ$, let $Γ⊆SL_2(ℤ)$ be a subgroup, let $F$ be the associated $q$-expansion function field, let $P$ be a place of $F$ with $deg(P)=1$, and let $n∈ℤ$. If $Fr$ denotes Frobenius on places and $Fr_*$ its divisor pushforward, then
--
--   $$Fr_*(n[P])=n[Fr(P)].$$
--
--   This gives the pointwise formula needed to compare Frobenius on divisors and on Picard classes.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.frobenius_pushforward_single_of_deg_one
    (K : Type*) [Field K] [PerfectField K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (P : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ))
    (hP : P.deg = 1) (n : ℤ) :
    ModularCurve.qExpFrobeniusDivPushforwardModL K Γ ℓ
        (Finsupp.single P n) =
      Finsupp.single
        (ModularCurve.qExpFrobeniusPlaceModL K Γ ℓ P) n := by sorry
