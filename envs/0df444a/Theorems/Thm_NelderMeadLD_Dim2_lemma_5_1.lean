-- Prove2me | Theorems.Thm_NelderMeadLD_Dim2_lemma_5_1
-- name    : NelderMeadLD.Dim2.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:50.621841+00:00
-- url     : https://prove2.me/theorems/27b5b220-4b89-47c2-a980-eec47e18e482
-- title:
--   Lemma 5.1, p. 136 — n = 2, ρ = 1, γ = ½: if the best vertex never moves, the triangles converge to it
-- statement:
--   Let $f:\mathbb R^2\to\mathbb R$ be strictly convex with bounded level sets (every set $\{x: f(x)\le\mu\}$ is bounded). Run Algorithm NM on $f$ with reflection coefficient $\rho=1$, contraction coefficient $\gamma=\tfrac12$, and any $\chi,\sigma$ satisfying (2.1), from a nondegenerate initial triangle $\Delta_0$. If the best vertex is constant, $x_1^{(k)}=x_1^{(0)}$ for all $k$, then every vertex converges to it:
--   $$\lim_{k\to\infty}x_i^{(k)}=x_1^{(0)}\qquad(i=1,2,3).$$
--
--   This is the case of Theorem 5.1 not covered by Corollary 3.1; it describes the behaviour seen in McKinnon's examples, where the simplices converge to a nonstationary point.
--
--   **Formalization Note** Vertices $x_1,x_2,x_3$ are Lean indices `0,1,2`. The lemma names only $\rho=1$ and $\gamma=\tfrac12$; since the best vertex never changes, no expansion is ever accepted, so $\chi$ is kept general under (2.1) rather than fixed at the §5 standard value $2$. Likewise $\sigma\in(0,1)$ is general (the paper's standard (2.2) has $\sigma=\tfrac12$) because no shrink occurs on a strictly convex $f$ (Lemma 3.5). Both choices make the statement at least as strong as the page's.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 136, Lemma 5.1

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_5_1 (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) (χ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK 1 χ (1 / 2) σ)
    (Δ : ℕ → Fin 3 → E 2) (hrun : IsNMRun f 1 χ (1 / 2) σ Δ) (hnd : Nondegenerate (Δ 0))
    (hconst : ∀ k, Δ k 0 = Δ 0 0) :
    ∀ i, Tendsto (fun k => Δ k i) atTop (𝓝 (Δ 0 0)) := by sorry

end NelderMeadLD.Dim2
