-- Prove2me | Theorems.Thm_N25_Endgame_exists_frobeniusLift25
-- name    : N25.Endgame.exists_frobeniusLift25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:11.409023+00:00
-- url     : https://prove2.me/theorems/d0a000fa-38ba-482a-a6a2-de7e6d1d4055
-- title:
--   Every reduction datum admits a global Frobenius lift
-- statement:
--   Let $ℓ$ be prime and let $D$ be a level-$25$ reduction datum whose valuation ring $A=D.A$ lies above $ℓ$. Then there exists an element $σ∈Gal(\overline{ℚ}/ℚ)$ that is Frobenius at $A$ over $ℓ$:
--
--   $$∃σ∈Gal(\overline{ℚ}/ℚ),\quad A\text{ is Frobenius at }σ\text{ over }ℓ.$$
--
--   This connects arithmetic Galois invariance of rational classes with Frobenius invariance after reduction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.exists_frobeniusLift25
    {ℓ : ℕ} [Fact ℓ.Prime] (D : RedDatum25 ℓ) :
    ∃ σ : N25.Gal, D.A.IsFrobeniusAt σ ℓ := by sorry
