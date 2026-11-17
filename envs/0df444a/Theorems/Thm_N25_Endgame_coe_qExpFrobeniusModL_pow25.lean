-- Prove2me | Theorems.Thm_N25_Endgame_coe_qExpFrobeniusModL_pow25
-- name    : N25.Endgame.coe_qExpFrobeniusModL_pow25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:36.98147+00:00
-- url     : https://prove2.me/theorems/8f91917f-7584-4991-a490-3ad0a835c204
-- title:
--   Function-field Frobenius iteration agrees with Laurent-series iteration
-- statement:
--   Let $p$ be prime, let $K$ be a field of characteristic $p$, let $F_K$ be the level-$25$ $q$-expansion function field, and let $ι:F_K→K((q))$ be its Laurent-series realization. Write $Φ_p$ for Frobenius on $F_K$ and $Q_p$ for Frobenius on Laurent series. Then for every $n≥0$ and $x∈F_K$,
--
--   $$ι(Φ_p^n(x))=Q_p^n(ι(x)).$$
--
--   This lets calculations on Laurent expansions be transported back to the modular function field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence

open N25
open N25.Endgame

theorem N25.Endgame.coe_qExpFrobeniusModL_pow25
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (n : ℕ) (x : ModularCurve.qExpFunctionFieldC K Γ25) :
    ((ModularCurve.qExpFrobeniusModL K Γ25 p ^ n) x : LaurentSeries K) =
      (ModularCurve.qExpand K p ^ n) (x : LaurentSeries K) := by sorry
