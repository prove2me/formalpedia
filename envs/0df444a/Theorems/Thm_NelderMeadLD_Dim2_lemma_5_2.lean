-- Prove2me | Theorems.Thm_NelderMeadLD_Dim2_lemma_5_2
-- name    : NelderMeadLD.Dim2.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:56.790722+00:00
-- url     : https://prove2.me/theorems/8d5f94d9-5ddf-46c1-92ea-cc4900ce1407
-- title:
--   Lemma 5.2, p. 142 — standard Nelder–Mead (ρ = 1, χ = 2, γ = ½) on a strictly convex f on ℝ²: vol(Δₖ) → 0
-- statement:
--   Let $f:\mathbb R^2\to\mathbb R$ be strictly convex with bounded level sets, and run Algorithm NM on $f$ with reflection coefficient $\rho=1$, expansion coefficient $\chi=2$, contraction coefficient $\gamma=\tfrac12$ and any shrink coefficient $0<\sigma<1$, from a nondegenerate initial triangle $\Delta_0$. Then the triangles collapse in area:
--   $$\lim_{k\to\infty}\operatorname{vol}(\Delta_k)=0\qquad(5.22).$$
--
--   The limit triangles may still be nondegenerate segments; Theorem 5.2 rules that out.
--
--   **Formalization Note** $\operatorname{vol}(\Delta)=|\det M|/2$ with $M$ the $2\times2$ edge matrix (2.10). The standard value $\sigma=\tfrac12$ of (2.2) is generalized to $0<\sigma<1$; no shrink occurs on a strictly convex $f$ (Lemma 3.5), so this changes nothing.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 142, Lemma 5.2, (5.22)

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_5_2 (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (Δ : ℕ → Fin 3 → E 2) (hrun : IsNMRun f 1 2 (1 / 2) σ Δ) (hnd : Nondegenerate (Δ 0)) :
    Tendsto (fun k => vol (Δ k)) atTop (𝓝 0) := by sorry

end NelderMeadLD.Dim2
