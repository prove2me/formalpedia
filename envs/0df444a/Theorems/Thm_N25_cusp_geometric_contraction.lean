-- Prove2me | Theorems.Thm_N25_cusp_geometric_contraction
-- name    : N25.cusp_geometric_contraction
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:45.046396+00:00
-- url     : https://prove2.me/theorems/856c9d3e-9dc8-4384-8fd4-4a6cd93f29aa
-- title:
--   Every geometric cusp contracts to a unique rational cusp
-- statement:
--   Let $P$ be a geometric place at which the embedded modular $j$-function has a pole. Then there exists a unique rational cusp $Q$ whose valuation ring is the contraction of that of $P$:
--
--   $$\exists!Q,\qquad Q\text{ is a cusp and }\mathcal O_Q=\mathcal O_P\cap F_{\mathbb Q}.$$
--
--   This identifies geometric cusps with points lying over uniquely determined rational closed cusps.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.cusp_geometric_contraction (P : GPlace)
    (hP : ModularCurve.IsCusp (emb25 j25) P) :
    ∃! Q : QPlace, ModularCurve.IsCusp j25 Q ∧
      Q.toValuationSubring = P.toValuationSubring.comap emb25.toRingHom := by sorry
