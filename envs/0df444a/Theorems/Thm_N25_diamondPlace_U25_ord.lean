-- Prove2me | Theorems.Thm_N25_diamondPlace_U25_ord
-- name    : N25.diamondPlace_U25_ord
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:56.410067+00:00
-- url     : https://prove2.me/theorems/a11cf5e4-61c5-4380-b24f-24f147697674
-- title:
--   Diamond transport cyclically shifts modular-unit orders
-- statement:
--   Let $\gamma$ be the label-$13$ diamond automorphism, let $P$ be a geometric place, and let $U_i$ be the $i$th embedded modular unit. Under the induced action of $\gamma$ on places,
--
--   $$\operatorname{ord}_{\gamma P}(U_i)=\operatorname{ord}_P(U_{i+1}).$$
--
--   This transports the divisor table of one unit around the five-cusp orbit.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Units
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option autoImplicit false
open N25

theorem N25.diamondPlace_U25_ord (i : Fin 5) (P : N25.Endgame.GPlace) :
    let γ := ModularCurve.diamondAutHBar 25 N25.H25 (ZMod.unitOfCoprime 13 (by decide))
    (AlgebraicCurve.SemilinearAut.ofAlgAut γ • P).ord (N25.Endgame.emb25 (U25 i)) =
      P.ord (N25.Endgame.emb25 (U25 (i+1))) := by sorry
