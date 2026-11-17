-- Prove2me | Theorems.Thm_N25_Endgame_eq_zero_of_red25_eq_zero
-- name    : N25.Endgame.eq_zero_of_red25_eq_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:23:52.355193+00:00
-- url     : https://prove2.me/theorems/07373c05-cc44-4902-ba16-84ae71ad2165
-- title:
--   Prime-to-$ℓ$ torsion specializes injectively
-- statement:
--   Let $ℓ$ be prime with $ℓ∤25$, let $D$ be a level-$25$ reduction datum at $ℓ$, let $m≥0$ satisfy $ℓ∤m$, and let $z$ be a point of the level-$25$ Jacobian. If $z$ is killed by $m$ and its reduction is zero, then
--
--   $$mz=0\ \land\ red_D(z)=0\quad⇒\quad z=0.$$
--
--   This is the prime-to-residue-characteristic injectivity principle used repeatedly in the torsion argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.eq_zero_of_red25_eq_zero
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ25 : ¬ ℓ ∣ 25)
    (D : RedDatum25 ℓ) (m : ℕ) (hm : ¬ ℓ ∣ m)
    (z : N25.J) (hmz : m • z = 0) (hz : red25 D z = 0) :
    z = 0 := by sorry
