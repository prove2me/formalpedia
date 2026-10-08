-- Prove2me | Theorems.Thm_ManPG_Conv_lemma_5_2_run
-- name    : ManPG.Conv.lemma_5_2_run
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:38.483226+00:00
-- url     : https://prove2.me/theorems/6aa47e3b-f4e5-4244-b6c3-c6c9e8f7a66d
-- title:
--   Lemma 5.2 along a run — γ·min{1, ᾱ} ≤ α_k ≤ 1 and F(X_{k+1}) − F(X_k) ≤ −α_k‖V_k‖²_F/(2t)
-- statement:
--   Let $f,\nabla f,h$ satisfy the standing assumptions of problem (1.1) on $\mathcal M=\mathrm{St}(n,r)$ with constants $L$, $L_h$. Let $\mathrm{Retr}$ be a retraction with constants $M_1,M_2>0$ in (3.1)–(3.2), and let $G>0$ bound $\|\nabla f\|_F$ on $\mathcal M$. Let $\gamma\in(0,1)$ and $t>0$, and let $(X_k),(V_k),(\alpha_k)$ be a run of Algorithm 1 (ManPG). With
--   $$\bar\alpha=\frac1{2(c_0+L_hM_2)t},\qquad c_0=M_2G+\frac{LM_1^2}{2},$$
--   every iteration $k\ge0$ satisfies
--   $$\gamma\min\{1,\bar\alpha\}\le\alpha_k\le1\qquad\text{and}\qquad F(X_{k+1})-F(X_k)\le-\frac{\alpha_k}{2t}\|V_k\|_F^2.$$
--
--   This is Lemma 5.2 in the form in which the proof of Theorem 5.5 uses it: the accepted stepsizes are bounded away from zero, and $F$ decreases monotonically along the iterates.
--
--   **Formalization Note** The proof of Theorem 5.5 writes $\alpha_k\ge\gamma\bar\alpha$. For a general $t>0$ the constant $\bar\alpha$ may exceed $1$, and then $\alpha_k=1<\gamma\bar\alpha$ is possible. The lower bound is therefore stated with $\gamma\min\{1,\bar\alpha\}$. With $t=1/L$ one has $\bar\alpha\le1$ whenever $V_k\neq0$ can occur, and then the two forms agree.
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), pp. 12–13, Lemma 5.2; its use in the proof of Theorem 5.5, p. 13 ("From Lemma 5.2, we know that α_k ≥ γᾱ")

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic
import Definitions.Def_ManPG_Conv_Setting

open scoped Matrix
open Filter Topology ProjLikeRetr.Stiefel

namespace ManPG.Conv

/-- Lemma 5.2, p. 12, along a run of Algorithm 1 (the form used in the proof of Theorem 5.5): every
accepted stepsize satisfies `γ · min{1, ᾱ} ≤ α_k ≤ 1`, and
`F(X_{k+1}) − F(X_k) ≤ −α_k/(2t) · ‖V_k‖_F²`. -/
theorem lemma_5_2_run {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ)
    (R : Mat n r → Mat n r → Mat n r) (L Lh M1 M2 G : ℝ)
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    (γ t : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t)
    (X V : ℕ → Mat n r) (α : ℕ → ℝ) (hrun : IsManPGRun f gradf h R γ t X V α) (k : ℕ) :
    γ * min 1 (abar L Lh M1 M2 G t) ≤ α k ∧ α k ≤ 1 ∧
      f (X (k + 1)) + h (X (k + 1)) - (f (X k) + h (X k)) ≤ -(α k / (2 * t)) * frobNorm (V k) ^ 2 := by sorry

end ManPG.Conv
