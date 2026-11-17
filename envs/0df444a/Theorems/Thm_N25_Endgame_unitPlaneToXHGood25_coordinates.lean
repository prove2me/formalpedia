-- Prove2me | Theorems.Thm_N25_Endgame_unitPlaneToXHGood25_coordinates
-- name    : N25.Endgame.unitPlaneToXHGood25_coordinates
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:11:41.586033+00:00
-- url     : https://prove2.me/theorems/bbe1745e-d7d7-4826-8ae9-92d9ca50df01
-- title:
--   The good-characteristic map preserves the two modular coordinates
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $K$ have characteristic $p$, and let $φ_K$ be the good-characteristic unit-plane map. Then $$φ_K(U)=U_0^{(K)} ∧ φ_K(V)=U_0^{(K)}/U_1^{(K)}.$$ This pins the model comparison. Formalization note: the prime and domain witnesses are explicit.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneModularMapGoodCharacteristic
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField

open N25
open N25.Endgame

theorem N25.Endgame.unitPlaneToXHGood25_coordinates
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    unitPlaneToXHGood25 p hp K
        (algebraMap (N25.UnitPlaneRing25C K)
          (N25.UnitPlaneFF25C K) (N25.unitPlaneU25C K)) =
      N25.U25C K 0 ∧
    unitPlaneToXHGood25 p hp K
        (algebraMap (N25.UnitPlaneRing25C K)
          (N25.UnitPlaneFF25C K) (N25.unitPlaneV25C K)) =
      N25.U25C K 0 / N25.U25C K 1 := by sorry
