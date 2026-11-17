-- Prove2me | Theorems.Thm_N25_Endgame_red_pointDiff25
-- name    : N25.Endgame.red_pointDiff25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:33.511196+00:00
-- url     : https://prove2.me/theorems/2d4e706c-d291-4735-a9cd-8e0975c51863
-- title:
--   Reduction preserves equal-degree point differences
-- statement:
--   Let $\ell$ be a prime, let $D$ be a level-$25$ reduction datum at $\ell$, and let $P,Q$ be places of the geometric level-$25$ function field with $\deg P=\deg Q$. Write $[P-Q]$ for their degree-zero divisor class, and write $\overline P,\overline Q$ for the reduced places supplied by $D$. Then
--
--   $$\operatorname{red}_D([P-Q])=[\overline P-\overline Q].$$
--
--   This compatibility transports geometric point differences into the special-fiber Jacobian. Formalization note: the displayed class on the right uses the degree equality obtained by transporting $\deg P=\deg Q$ through preservation of place degrees under reduction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_redPlace25_degree
import Definitions.Def_N25_Endgame

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.red_pointDiff25
    {ℓ : ℕ} [Fact ℓ.Prime] (D : RedDatum25 ℓ)
    (P Q : GPlace) (hdeg : P.deg = Q.deg) :
    red25 D (pointDiff P Q hdeg) =
      pointDiff (redPlace25 D P) (redPlace25 D Q)
        ((redPlace25_degree D P).trans
          (hdeg.trans (redPlace25_degree D Q).symm)) := by sorry
