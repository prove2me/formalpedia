-- Prove2me | Theorems.Thm_NelderMeadLD_Dim2_theorem_5_2
-- name    : NelderMeadLD.Dim2.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:10.086996+00:00
-- url     : https://prove2.me/theorems/49a39db0-3b40-458a-8c80-060276b3f5d0
-- title:
--   Theorem 5.2, p. 144 — standard Nelder–Mead (ρ = 1, χ = 2, γ = ½) on a strictly convex f on ℝ² with bounded level sets: diam(Δₖ) → 0
-- statement:
--   Let $f:\mathbb R^2\to\mathbb R$ be strictly convex with bounded level sets, and run the standard Nelder–Mead method, Algorithm NM with reflection coefficient $\rho=1$, expansion coefficient $\chi=2$, contraction coefficient $\gamma=\tfrac12$ and any shrink coefficient $0<\sigma<1$, from a nondegenerate initial triangle $\Delta_0$. Then the diameters of the triangles tend to zero:
--   $$\lim_{k\to\infty}\operatorname{diam}(\Delta_k)=0\qquad(5.31),$$
--   where $\operatorname{diam}(\Delta_k)=\max_{i\ne j}\|x_i^{(k)}-x_j^{(k)}\|$.
--
--   The theorem does not assert that the triangles converge to a point, nor that their vertices approach the minimizer of $f$; McKinnon's examples show that the latter can fail.
--
--   **Formalization Note** The run is any sequence satisfying the iteration relation (the paper leaves the ordering after a shrink partly open; on a strictly convex $f$ no shrink occurs). The standard value $\sigma=\tfrac12$ of (2.2) is generalized to $0<\sigma<1$, which changes nothing for the same reason. The diameter is a finite maximum of Euclidean distances between vertices.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 144, Theorem 5.2, (5.31)

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem theorem_5_2 (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (Δ : ℕ → Fin 3 → E 2) (hrun : IsNMRun f 1 2 (1 / 2) σ Δ) (hnd : Nondegenerate (Δ 0)) :
    Tendsto (fun k => diam (Δ k)) atTop (𝓝 0) := by sorry

end NelderMeadLD.Dim2
