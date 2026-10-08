-- Prove2me | Theorems.Thm_NelderMeadLD_Conv1D_lemma_4_4
-- name    : NelderMeadLD.Conv1D.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:09.540027+00:00
-- url     : https://prove2.me/theorems/b219fa9a-a2df-4ff6-8cb8-50fed81bc86c
-- title:
--   Lemma 4.4, p. 128 — the limiting vertex values coincide: f*₁ = f*₂
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ be strictly convex with bounded level sets and minimizer $x_{\min}$. Let the parameters satisfy (2.1) (in particular $\rho > 0$ and $0 < \gamma < 1$), and let $\Delta_k = (x_1^{(k)}, x_2^{(k)})$ be the one-dimensional Nelder–Mead run from a nondegenerate, ordered initial interval. Then the vertex values $f_1^{(k)} = f(x_1^{(k)})$ and $f_2^{(k)} = f(x_2^{(k)})$ converge to a common limit:
--   $$f_1^* = \lim_{k\to\infty} f_1^{(k)} = \lim_{k\to\infty} f_2^{(k)} = f_2^*.$$
--
--   This excludes the situation in which the best vertex stalls while the worst vertex keeps a strictly larger value, and it is the starting point for showing that the interval shrinks to a point.
--
--   **Formalization Note** The page writes $f_1^* = f_2^*$, the existence of the limits being established earlier (Lemma 3.3); here the existence of a common limit $L$ of both sequences is part of the conclusion. No condition on $\rho\chi$ is assumed; the lemma's own hypotheses are $\rho > 0$, $0 < \gamma < 1$, and $\chi > 1$, $\chi > \rho$, $0 < \sigma < 1$ come from the standing conditions (2.1) of the one-dimensional analysis.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 128, Lemma 4.4

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem lemma_4_4 (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    ∃ L : ℝ, Tendsto (fun k => f (run f ρ χ γ σ p0 k).1) atTop (𝓝 L) ∧
      Tendsto (fun k => f (run f ρ χ γ σ p0 k).2) atTop (𝓝 L) := by sorry

end NelderMeadLD.Conv1D
