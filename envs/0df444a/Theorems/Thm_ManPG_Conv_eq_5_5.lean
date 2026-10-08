-- Prove2me | Theorems.Thm_ManPG_Conv_eq_5_5
-- name    : ManPG.Conv.eq_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:45.529042+00:00
-- url     : https://prove2.me/theorems/d26839fc-520f-4ef0-b21a-219f0b3c6361
-- title:
--   (5.5) — f(Retr_X(αV)) − f(X) ≤ α⟨∇f(X), V⟩ + c₀α²‖V‖²_F with c₀ = M₂G + LM₁²/2
-- statement:
--   Let $f,\nabla f,h$ satisfy the standing assumptions of problem (1.1) on $\mathcal M=\mathrm{St}(n,r)$ (in particular $\nabla f$ is $L$-Lipschitz). Let $\mathrm{Retr}$ be a retraction with constants $M_1,M_2>0$ in (3.1)–(3.2), and let $G>0$ bound $\|\nabla f(X)\|_F$ on $\mathcal M$. Then for every $X\in\mathcal M$, every tangent vector $V\in T_X\mathcal M$ and every $\alpha>0$,
--   $$f(\mathrm{Retr}_X(\alpha V))-f(X)\le\alpha\langle\nabla f(X),V\rangle+c_0\alpha^2\|V\|_F^2,\qquad c_0=M_2G+\frac{LM_1^2}{2}.\tag{5.5}$$
--
--   This is the smooth part of the sufficient-decrease estimate of Lemma 5.2. It extends the Lipschitz-type bound for pullbacks $f\circ\mathrm{Retr}_X$ from Boumal et al. to the setting of ManPG.
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), p. 12, §5, proof of Lemma 5.2, (5.5)

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic
import Definitions.Def_ManPG_Conv_Setting

open scoped Matrix
open Filter Topology ProjLikeRetr.Stiefel

namespace ManPG.Conv

/-- (5.5), proof of Lemma 5.2, p. 12: for `X ∈ M`, a tangent direction `V ∈ T_X M` and any `α > 0`,
`f(Retr_X(αV)) − f(X) ≤ α⟨∇f(X), V⟩ + c₀α²‖V‖_F²`, where `c₀ = M₂G + LM₁²/2`. -/
theorem eq_5_5 {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ)
    (R : Mat n r → Mat n r → Mat n r) (L Lh M1 M2 G : ℝ)
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    (X V : Mat n r) (hX : X ∈ stiefel n r) (hV : V ∈ tangent X) (α : ℝ) (hα : 0 < α) :
    f (R X (α • V)) - f X ≤ α * frobInner (gradf X) V + c0 L M1 M2 G * α ^ 2 * frobNorm V ^ 2 := by sorry

end ManPG.Conv
