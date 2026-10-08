-- Prove2me | Theorems.Thm_ManPG_Conv_lemma_5_3
-- name    : ManPG.Conv.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:33.428188+00:00
-- url     : https://prove2.me/theorems/701f6762-ece8-4065-9344-096a76e98027
-- title:
--   Lemma 5.3 — if V_k = 0 then X_k is a stationary point of (1.1)
-- statement:
--   Let $f,\nabla f,h$ satisfy the standing assumptions of problem (1.1) on $\mathcal M=\mathrm{St}(n,r)$, let $t>0$ and $X\in\mathcal M$. If $V=0$ solves the ManPG subproblem (4.3) at $X$, i.e. $0$ minimizes
--   $$V\mapsto\langle\nabla f(X),V\rangle+\frac1{2t}\|V\|_F^2+h(X+V)$$
--   over the tangent space $T_X\mathcal M$, then $X$ is a stationary point of (1.1) in the sense of Definition 3.3:
--   $$0\in\operatorname{grad}f(X)+\operatorname{Proj}_{T_X\mathcal M}\big(\partial h(X)\big).$$
--
--   The lemma justifies $\|V_k\|_F$ as a stationarity measure for ManPG, and hence the stopping test $\|V_k\|_F\le\varepsilon/L$ and the definition of $\varepsilon$-stationarity (Definition 5.4).
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), p. 13, Lemma 5.3

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic
import Definitions.Def_ManPG_Conv_Setting

open scoped Matrix
open Filter Topology ProjLikeRetr.Stiefel

namespace ManPG.Conv

/-- Lemma 5.3, p. 13: if `V = 0` solves the subproblem (4.3) at `X ∈ M` (for some stepsize
`t > 0`), then `X` is a stationary point of (1.1) (Definition 3.3). -/
theorem lemma_5_3 {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ)
    (L Lh : ℝ) (hA : StandingAssumptions f gradf h L Lh)
    (t : ℝ) (ht : 0 < t) (X : Mat n r) (hX : X ∈ stiefel n r) (h0 : IsSubSol gradf h X t 0) :
    IsStationary gradf h X := by sorry

end ManPG.Conv
