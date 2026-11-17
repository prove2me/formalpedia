-- Prove2me | Theorems.Thm_N25_cusp_galois_contraction
-- name    : N25.cusp_galois_contraction
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:55.650199+00:00
-- url     : https://prove2.me/theorems/b946a98a-43f6-4c47-91af-39c938b5cc7b
-- title:
--   Arithmetic Galois action preserves the contracted rational place
-- statement:
--   Let $\sigma\in\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and let $P$ be a geometric place of the level-$25$ function field. The arithmetic Galois translate $\sigma P$ has the same contraction to the rational function field as $P$:
--
--   $$\mathcal O_{\sigma P}\cap F_{\mathbb Q}=\mathcal O_P\cap F_{\mathbb Q}.$$
--
--   This shows that geometric places in one Galois orbit lie over the same rational closed place.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open scoped Pointwise
open N25
open N25.Endgame

theorem N25.cusp_galois_contraction (σ : Gal) (P : GPlace) :
    (arithmeticGalois FQ σ • P).toValuationSubring.comap emb25.toRingHom =
      P.toValuationSubring.comap emb25.toRingHom := by sorry
