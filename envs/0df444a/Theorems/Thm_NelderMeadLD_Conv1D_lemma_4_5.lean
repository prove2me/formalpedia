-- Prove2me | Theorems.Thm_NelderMeadLD_Conv1D_lemma_4_5
-- name    : NelderMeadLD.Conv1D.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:08.561785+00:00
-- url     : https://prove2.me/theorems/4f08d263-65f3-4ee8-8487-21b7294ad052
-- title:
--   Lemma 4.5, p. 129 — the diameter of the 1-D Nelder–Mead interval tends to 0
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ be strictly convex with bounded level sets and minimizer $x_{\min}$. Let the parameters satisfy (2.1) (in particular $\rho > 0$ and $0 < \gamma < 1$), and let $\Delta_k = (x_1^{(k)}, x_2^{(k)})$ be the one-dimensional Nelder–Mead run from a nondegenerate, ordered initial interval $\Delta_0$. Then
--   $$\lim_{k\to\infty} \operatorname{diam}(\Delta_k) = 0, \qquad \operatorname{diam}(\Delta_k) = |x_1^{(k)} - x_2^{(k)}|.$$
--
--   The interval always collapses to a point, whatever the value of $\rho\chi$; whether that point is the minimizer is the subject of Theorem 4.1.
--
--   **Formalization Note** No condition on $\rho\chi$ is assumed. As in Lemma 4.4, $\chi > 1$, $\chi > \rho$ and $0 < \sigma < 1$ come from the standing conditions (2.1).
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 129, Lemma 4.5

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem lemma_4_5 (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    Tendsto (fun k => diam (run f ρ χ γ σ p0 k)) atTop (𝓝 0) := by sorry

end NelderMeadLD.Conv1D
