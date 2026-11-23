-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_proposition_3
-- name    : LogBarrierIPM.Iterations.Supplement.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:12:14.616681+00:00
-- url     : https://prove2.me/theorems/6eead70e-3edd-415d-b62a-698812a9902d
-- title:
--   Proposition 3 — specialization of finite generators
-- statement:
--   Let $d\ge1$, let $\mathcal P=\{x\in K^d:Ax\le b\}$, and suppose $\mathcal P=\operatorname{conv}_K\{u^1,\ldots,u^q\}+\operatorname{cone}_K\{v^1,\ldots,v^r\}$. Then, for every sufficiently large real $t$,
--   $$\mathcal P(t)=\operatorname{conv}_{\mathbb R}\{u^1(t),\ldots,u^q(t)\}+\operatorname{cone}_{\mathbb R}\{v^1(t),\ldots,v^r(t)\}.$$
--   The number of points or rays may be zero; no orthant hypothesis is imposed. This supplies the generator specialization used in Theorem 9.
--
--   Differences from the source:
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
--   - encoding: vectors indexed from 1 → 0-based Fin vectors; reason: the index shift preserves every coordinate
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 8, Proposition 3

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_PuiseuxGeometry

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem proposition_3 {p d q r : ℕ} (hd : 1 ≤ d)
    (A : Matrix (Fin p) (Fin d) Puiseux) (b : Fin p → Puiseux)
    (u : Fin q → Fin d → Puiseux) (v : Fin r → Fin d → Puiseux)
    (hgen : kPolyhedron A b = kGenerated u v) :
    ∀ᶠ t in atTop, realPolyhedron A b t =
      realGenerated (fun i => evalFun (u i) t) (fun j => evalFun (v j) t) := by sorry

end LogBarrierIPM.Iterations.Supplement
