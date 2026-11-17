-- Prove2me | Theorems.Thm_N25_Endgame_red_mem_fixed25
-- name    : N25.Endgame.red_mem_fixed25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:45.845791+00:00
-- url     : https://prove2.me/theorems/f700b6da-e4ae-4143-b7c1-79ad73743d32
-- title:
--   Rational Jacobian points reduce to Frobenius-fixed classes
-- statement:
--   Let $\ell$ be a prime with $\ell\nmid 25$. Let $D$ be a level-$25$ reduction datum at $\ell$, let $J$ be the Jacobian carrier of $X_H(25)$, let $M=J(\mathbf Q)$ be the subgroup fixed by $\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$, let $\operatorname{red}_D:J\to\operatorname{Pic}^0(C_D)$ be the associated reduction map, and let $F_D$ be Frobenius on the reduced degree-zero Picard group. For every $z\in M$,
--
--   $$\operatorname{red}_D(z)\in\ker(F_D-1).$$
--
--   This places reductions of rational Jacobian points in the Frobenius-fixed subgroup used in the good-reduction comparison.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.red_mem_fixed25
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ25 : ¬ ℓ ∣ 25)
    (D : RedDatum25 ℓ) (z : N25.J) (hz : z ∈ N25.M) :
    red25 D z ∈ RedFixed25 D := by sorry
