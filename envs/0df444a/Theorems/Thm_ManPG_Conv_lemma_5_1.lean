-- Prove2me | Theorems.Thm_ManPG_Conv_lemma_5_1
-- name    : ManPG.Conv.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:38.896628+00:00
-- url     : https://prove2.me/theorems/8d8e1b94-87eb-47a8-a4ff-e94c47a85017
-- title:
--   Lemma 5.1 — g(αV_k) − g(0) ≤ (α − 2)α‖V_k‖²_F/(2t) for α ∈ [0, 1]
-- statement:
--   Let $f,\nabla f,h$ satisfy the standing assumptions of problem (1.1) on $\mathcal M=\mathrm{St}(n,r)$, let $t>0$, and let $X\in\mathcal M$. Let
--   $$g(V)=\langle\nabla f(X),V\rangle+\frac1{2t}\|V\|_F^2+h(X+V)\tag{5.1}$$
--   be the objective of the ManPG subproblem (4.3) at $X$, and let $V^\star$ be a solution of (4.3), i.e. a minimizer of $g$ over the tangent space $T_X\mathcal M$. Then for every $\alpha\in[0,1]$,
--   $$g(\alpha V^\star)-g(0)\le\frac{(\alpha-2)\alpha}{2t}\,\|V^\star\|_F^2.\tag{5.2}$$
--
--   The right-hand side is negative for $\alpha\in(0,1]$ unless $V^\star=0$, so the subproblem solution is a descent direction for the subproblem's objective. This is the first step of the convergence analysis of ManPG.
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), p. 11, Lemma 5.1, (5.1)–(5.2)

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic
import Definitions.Def_ManPG_Conv_Setting

open scoped Matrix
open Filter Topology ProjLikeRetr.Stiefel

namespace ManPG.Conv

/-- Lemma 5.1, p. 11: if `V` solves the subproblem (4.3) at `X ∈ M`, then for every `α ∈ [0, 1]`,
`g(αV) − g(0) ≤ (α − 2)α/(2t) · ‖V‖_F²` (5.2), with `g` the objective (5.1). -/
theorem lemma_5_1 {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ)
    (L Lh : ℝ) (hA : StandingAssumptions f gradf h L Lh)
    (t : ℝ) (ht : 0 < t) (X V : Mat n r) (hX : X ∈ stiefel n r)
    (hV : IsSubSol gradf h X t V) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    subObj gradf h X t (α • V) - subObj gradf h X t 0 ≤ (α - 2) * α / (2 * t) * frobNorm V ^ 2 := by sorry

end ManPG.Conv
