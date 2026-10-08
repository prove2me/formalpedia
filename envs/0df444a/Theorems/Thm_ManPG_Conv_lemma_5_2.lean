-- Prove2me | Theorems.Thm_ManPG_Conv_lemma_5_2
-- name    : ManPG.Conv.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:36.345176+00:00
-- url     : https://prove2.me/theorems/f1451a07-69d9-4058-8343-66632249a28b
-- title:
--   Lemma 5.2 — sufficient decrease F(Retr_X(αV)) − F(X) ≤ −α‖V‖²_F/(2t) for 0 < α ≤ min{1, ᾱ}
-- statement:
--   Let $f,\nabla f,h$ satisfy the standing assumptions of problem (1.1) on $\mathcal M=\mathrm{St}(n,r)$ with constants $L$, $L_h$. Let $\mathrm{Retr}$ be a retraction with constants $M_1,M_2>0$ in (3.1)–(3.2), and let $G>0$ bound $\|\nabla f\|_F$ on $\mathcal M$. Fix $t>0$ and put
--   $$c_0=M_2G+\frac{LM_1^2}{2},\qquad \bar\alpha=\frac{1}{2(c_0+L_hM_2)t}.$$
--   Let $X\in\mathcal M$ and let $V$ solve the ManPG subproblem (4.3) at $X$ with stepsize $t$. Then for every $0<\alpha\le\min\{1,\bar\alpha\}$, with $F=f+h$,
--   $$F(\mathrm{Retr}_X(\alpha V))-F(X)\le-\frac{\alpha}{2t}\|V\|_F^2.$$
--
--   This is the sufficient-decrease content of Lemma 5.2, with the explicit constant $\bar\alpha$ from its proof. It shows that every stepsize in $(0,\min\{1,\bar\alpha\}]$ passes the Armijo test of Algorithm 1. Iteration complexity bounds rest on this estimate.
--
--   **Formalization Note** The paper states Lemma 5.2 as "for any $0<\alpha\le\min\{1,\bar\alpha\}$ … the sequence $\{X_k\}$ satisfies $F(X_{k+1})-F(X_k)\le-\frac{\alpha}{2t}\|V_k\|_F^2$". Its proof shows the inequality for the trial point $\mathrm{Retr}_{X_k}(\alpha V_k)$ at every such $\alpha$, which is what is stated here. The sequence form, with the accepted stepsize $\alpha_k$, and the well-definedness of the line search are separate milestones.
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), pp. 12–13, Lemma 5.2 and its proof (ᾱ = 1/(2(c₀ + L_hM₂)t))

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic
import Definitions.Def_ManPG_Conv_Setting

open scoped Matrix
open Filter Topology ProjLikeRetr.Stiefel

namespace ManPG.Conv

/-- Lemma 5.2, pp. 12–13 (sufficient decrease, as proved): if `V` solves (4.3) at `X ∈ M` with
stepsize `t > 0`, then for every `0 < α ≤ min{1, ᾱ}` with `ᾱ = 1/(2(c₀ + L_h M₂)t)`,
`F(Retr_X(αV)) − F(X) ≤ −α/(2t) · ‖V‖_F²`, where `F = f + h`. -/
theorem lemma_5_2 {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ)
    (R : Mat n r → Mat n r → Mat n r) (L Lh M1 M2 G : ℝ)
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    (t : ℝ) (ht : 0 < t) (X V : Mat n r) (hX : X ∈ stiefel n r) (hV : IsSubSol gradf h X t V)
    (α : ℝ) (hα0 : 0 < α) (hα : α ≤ min 1 (abar L Lh M1 M2 G t)) :
    f (R X (α • V)) + h (R X (α • V)) - (f X + h X) ≤ -(α / (2 * t)) * frobNorm V ^ 2 := by sorry

end ManPG.Conv
