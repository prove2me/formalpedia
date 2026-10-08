-- Prove2me | Theorems.Thm_NelderMeadLD_Dim2_lemma_3_5
-- name    : NelderMeadLD.Dim2.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:51.198617+00:00
-- url     : https://prove2.me/theorems/dc066b31-645c-42dc-b86b-28b793dde1de
-- title:
--   Lemma 3.5, p. 122 — on a strictly convex function Algorithm NM never shrinks
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ ($n\ge1$) be strictly convex, i.e. $f(\lambda y+(1-\lambda)z)<\lambda f(y)+(1-\lambda)f(z)$ for $y\ne z$ and $0<\lambda<1$ (Definition 3.1). Let the coefficients satisfy (2.1) and let $(\Delta_k)$ be a run of Algorithm NM on $f$ from a nondegenerate initial simplex $\Delta_0$. Then
--   $$\text{no iteration } k \text{ of the run is a shrink step.}$$
--
--   This is why the shrink coefficient $\sigma$ plays no role in the analysis of strictly convex functions.
--
--   **Formalization Note** Strict convexity is `StrictConvexOn ℝ Set.univ f`. A shrink at iteration $k$ means that the case analysis of steps 2–4 applied to $\Delta_k$ ends in step 5.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 122, Lemma 3.5 (Definition 3.1)

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_3_5 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hf : StrictConvexOn ℝ Set.univ f) :
    ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k := by sorry

end NelderMeadLD.Dim2
