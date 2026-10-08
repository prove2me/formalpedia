-- Prove2me | Theorems.Thm_NelderMeadLD_Dim2_theorem_5_1
-- name    : NelderMeadLD.Dim2.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:56.578201+00:00
-- url     : https://prove2.me/theorems/2f2ea005-dfc2-4249-9f94-d0427e4a6f15
-- title:
--   Theorem 5.1, p. 135 — n = 2, ρ = 1, γ = ½: the three limiting vertex values coincide, f*₁ = f*₂ = f*₃
-- statement:
--   Let $f:\mathbb R^2\to\mathbb R$ be strictly convex with bounded level sets. Run Algorithm NM on $f$ with reflection coefficient $\rho=1$, contraction coefficient $\gamma=\tfrac12$, and any $\chi,\sigma$ satisfying (2.1), from a nondegenerate initial triangle $\Delta_0$. Then the three vertex values converge to one common limit:
--   $$\exists\,L\in\mathbb R:\qquad \lim_{k\to\infty} f(x_i^{(k)})=L\quad(i=1,2,3),$$
--   i.e. $f_1^*=f_2^*=f_3^*$.
--
--   This is the first convergence result for the standard two-dimensional Nelder–Mead method; it does not say that $L$ is the minimum value of $f$.
--
--   **Formalization Note** The theorem names only $\rho=1$ and $\gamma=\tfrac12$; $\chi$ and $\sigma$ are kept general under (2.1) (§5's standing values are $\chi=2$, $\sigma=\tfrac12$), which is at least as strong as the page's statement. Existence of the limits is part of the conclusion.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 135, Theorem 5.1

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem theorem_5_1 (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) (χ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK 1 χ (1 / 2) σ)
    (Δ : ℕ → Fin 3 → E 2) (hrun : IsNMRun f 1 χ (1 / 2) σ Δ) (hnd : Nondegenerate (Δ 0)) :
    ∃ L : ℝ, ∀ i : Fin 3, Tendsto (fun k => f (Δ k i)) atTop (𝓝 L) := by sorry

end NelderMeadLD.Dim2
