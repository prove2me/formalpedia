-- Prove2me | Theorems.Thm_ManPG_Conv_telescoped_bound
-- name    : ManPG.Conv.telescoped_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:34.476842+00:00
-- url     : https://prove2.me/theorems/10a28e94-30e5-4d31-8ab0-b3304eecb5f8
-- title:
--   Proof of Theorem 5.5 — if ‖V_k‖_F > ε/L for k < K then F(X₀) − F* > tKε²γᾱ/2 (t = 1/L)
-- statement:
--   Let $f,\nabla f,h$ satisfy the standing assumptions of problem (1.1) on $\mathcal M=\mathrm{St}(n,r)$ with constants $L$, $L_h$. Let $\mathrm{Retr}$ be a retraction with constants $M_1,M_2>0$ in (3.1)–(3.2), let $G>0$ bound $\|\nabla f\|_F$ on $\mathcal M$, and let $\gamma\in(0,1)$, $t=1/L$, $\bar\alpha=1/(2(c_0+L_hM_2)t)$ with $c_0=M_2G+LM_1^2/2$. Let $(X_k),(V_k),(\alpha_k)$ be a run of Algorithm 1 (ManPG), let $F^*$ be the optimal value of (1.1), let $\varepsilon>0$ and $K\ge1$. Suppose the algorithm has not terminated after $K$ iterations, i.e. $\|V_k\|_F>\varepsilon/L$ for $k=0,1,\dots,K-1$. Then
--   $$F(X_0)-F^*\ge F(X_0)-F(X_K)\ge\frac t2\sum_{k=0}^{K-1}\alpha_k\Big\|\frac{V_k}{t}\Big\|_F^2>\frac{t\varepsilon^2}{2}\sum_{k=0}^{K-1}\alpha_k\ge\frac{tK\varepsilon^2}{2}\gamma\bar\alpha.$$
--
--   This chain is the counting argument behind the iteration bound $\lceil 2L(F(X_0)-F^*)/(\gamma\bar\alpha\varepsilon^2)\rceil$ of Theorem 5.5.
--
--   **Formalization Note** Each of the four inequalities is a separate conjunct. The hypothesis $K\ge1$ is needed for the strict inequality, which fails for $K=0$. The last link uses $\alpha_k\ge\gamma\bar\alpha$ as written in the paper. It holds here because $V_0\neq0$ and $t=1/L$ force $\bar\alpha\le1$.
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), p. 13, §5, proof of Theorem 5.5 (second display)

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic
import Definitions.Def_ManPG_Conv_Setting

open scoped Matrix
open Filter Topology ProjLikeRetr.Stiefel

namespace ManPG.Conv

/-- Proof of Theorem 5.5, p. 13: for a run of Algorithm 1 with `t = 1/L`, if `‖V_k‖_F > ε/L` for
`k = 0, 1, …, K − 1` (`K ≥ 1`), then, with `α_k` the accepted stepsizes and `F*` the optimal value,
`F(X₀) − F* ≥ F(X₀) − F(X_K) ≥ (t/2) Σ_{k<K} α_k‖V_k/t‖_F² > (tε²/2) Σ_{k<K} α_k ≥ (tKε²/2) γᾱ`. -/
theorem telescoped_bound {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r)
    (h : Mat n r → ℝ) (R : Mat n r → Mat n r → Mat n r) (L Lh M1 M2 G : ℝ)
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    (γ t : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (htL : t = 1 / L)
    (X V : ℕ → Mat n r) (α : ℕ → ℝ) (hrun : IsManPGRun f gradf h R γ t X V α)
    (Fstar : ℝ) (hFstar : IsOptimalValue f h Fstar) (ε : ℝ) (hε : 0 < ε)
    (K : ℕ) (hK : 1 ≤ K) (hfail : ∀ k < K, ε / L < frobNorm (V k)) :
    f (X 0) + h (X 0) - Fstar ≥ f (X 0) + h (X 0) - (f (X K) + h (X K)) ∧
    f (X 0) + h (X 0) - (f (X K) + h (X K))
      ≥ t / 2 * ∑ k ∈ Finset.range K, α k * frobNorm ((1 / t) • V k) ^ 2 ∧
    t / 2 * ∑ k ∈ Finset.range K, α k * frobNorm ((1 / t) • V k) ^ 2
      > t * ε ^ 2 / 2 * ∑ k ∈ Finset.range K, α k ∧
    t * ε ^ 2 / 2 * ∑ k ∈ Finset.range K, α k
      ≥ t * K * ε ^ 2 / 2 * (γ * abar L Lh M1 M2 G t) := by sorry

end ManPG.Conv
