-- Prove2me | Theorems.Thm_N25_Endgame_coe_redM25
-- name    : N25.Endgame.coe_redM25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:23:27.013663+00:00
-- url     : https://prove2.me/theorems/64b5cfb0-89ca-4f50-a13d-f1000bbe8220
-- title:
--   The rational reduction map has the expected underlying Picard class
-- statement:
--   Let $ℓ$ be prime with $ℓ∤25$, let $D$ be a reduction datum at $ℓ$, let $M$ be the rational fixed subgroup of the level-$25$ Jacobian, and let $z∈M$. The map $red_D^M:M→Pic^0_D{}^{Fr=1}$ is the reduction map with codomain restricted to Frobenius-fixed classes. After forgetting that fixed-point certificate,
--
--   $$red_D^M(z)=red_D(z)\quad\text{in }Pic^0_D.$$
--
--   This connects the restricted homomorphism used for injectivity with the original Jacobian reduction map. Formalization note: the statement only resolves nested subtype coercions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ReductionMap

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.coe_redM25
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ25 : ¬ ℓ ∣ 25)
    (D : RedDatum25 ℓ) (z : ↥N25.M) :
    ((redM25 hℓ25 D z : RedFixed25 D) : SpecialPic D.A) = red25 D z := by sorry
