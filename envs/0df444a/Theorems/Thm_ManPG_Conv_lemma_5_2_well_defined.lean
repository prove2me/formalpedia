-- Prove2me | Theorems.Thm_ManPG_Conv_lemma_5_2_well_defined
-- name    : ManPG.Conv.lemma_5_2_well_defined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:31.793979+00:00
-- url     : https://prove2.me/theorems/77dcce6e-58d0-4612-8530-5527da9c4488
-- title:
--   Lemma 5.2 — the line search of Algorithm 1 is well defined: ManPG runs forever from every X₀ ∈ St(n, r)
-- statement:
--   Let $f,\nabla f,h$ satisfy the standing assumptions of problem (1.1) on $\mathcal M=\mathrm{St}(n,r)$, and let $\mathrm{Retr}$ be a retraction with constants $M_1,M_2>0$ in (3.1)–(3.2). Let $\gamma\in(0,1)$ and $t>0$. Then for every initial point $X_0\in\mathcal M$ there are sequences $(X_k)_{k\ge0}$, $(V_k)_{k\ge0}$, $(\alpha_k)_{k\ge0}$ starting at $X_0$ that form a run of Algorithm 1 (ManPG). In such a run:
--   1. each $V_k$ solves the subproblem (4.3) at $X_k$;
--   2. each backtracking loop "while $F(\mathrm{Retr}_{X_k}(\alpha V_k))>F(X_k)-\alpha\|V_k\|_F^2/(2t)$ do $\alpha=\gamma\alpha$", started at $\alpha=1$, terminates, and $\alpha_k$ is the value at which it stops;
--   3. $X_{k+1}=\mathrm{Retr}_{X_k}(\alpha_kV_k)$.
--
--   This is the clause "the line search procedure in Algorithm 1 is well defined" of Lemma 5.2. It also guarantees that the statements about runs of ManPG are not vacuous.
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), p. 12, Lemma 5.2 ("the line search procedure in Algorithm 1 is well defined"); Algorithm 1, p. 9

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic
import Definitions.Def_ManPG_Conv_Setting

open scoped Matrix
open Filter Topology ProjLikeRetr.Stiefel

namespace ManPG.Conv

/-- Lemma 5.2, p. 12 ("the line search procedure in Algorithm 1 is well defined"): for every
`γ ∈ (0, 1)`, `t > 0` and initial point `X₀ ∈ M`, Algorithm 1 runs forever — every subproblem
(4.3) has a solution and every backtracking loop stops — so a run started at `X₀` exists. -/
theorem lemma_5_2_well_defined {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r)
    (h : Mat n r → ℝ) (R : Mat n r → Mat n r → Mat n r) (L Lh M1 M2 : ℝ)
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2)
    (γ t : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t) (X0 : Mat n r) (hX0 : X0 ∈ stiefel n r) :
    ∃ (X V : ℕ → Mat n r) (α : ℕ → ℝ), X 0 = X0 ∧ IsManPGRun f gradf h R γ t X V α := by sorry

end ManPG.Conv
