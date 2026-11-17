-- Prove2me | Theorems.Thm_N25_Endgame_nonempty_redDatum25
-- name    : N25.Endgame.nonempty_redDatum25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:23:59.654035+00:00
-- url     : https://prove2.me/theorems/ef2217f7-e42d-4171-a71c-4206e386411c
-- title:
--   Reduction data exist at every prime away from $25$
-- statement:
--   Let $ℓ$ be a prime with $ℓ∤25$. Then there exists a valuation ring of $\overline{ℚ}$ above $ℓ$, with residue characteristic $ℓ$ and the required level-$25$ $q$-expansion reduction inputs; equivalently,
--
--   $$RedDatum_{25}(ℓ)\neq∅.$$
--
--   This ensures that all good-prime reduction constructions used in the endgame can actually be instantiated.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.nonempty_redDatum25
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ25 : ¬ ℓ ∣ 25) :
    Nonempty (RedDatum25 ℓ) := by sorry
