-- Prove2me | Theorems.Thm_NelderMeadLD_Conv1D_lemma_4_3
-- name    : NelderMeadLD.Conv1D.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:58.27598+00:00
-- url     : https://prove2.me/theorems/05f31eb2-a795-4c7c-aa53-461f9c9e876d
-- title:
--   Lemma 4.3, p. 126 — with ρχ ≥ 1 the proximity property (4.4) is preserved from iteration k to k + 1
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ be strictly convex with bounded level sets and minimizer $x_{\min}$. Let the parameters satisfy (2.1) and $\rho\chi \ge 1$, and let $\Delta_k = (x_1^{(k)}, x_2^{(k)})$ be the one-dimensional Nelder–Mead run from a nondegenerate, ordered initial interval. Define
--   $$N_{NM} = \max\Big(\frac{1}{\rho\gamma},\ \frac{\rho}{\gamma},\ \rho\chi,\ \chi - 1\Big) \tag{4.3}$$
--   and say that the **proximity property** holds at iteration $k$ if
--   $$x_{\min} \in \operatorname{int}\big(x_2^{(k)},\ x_1^{(k)} + N_{NM}(x_1^{(k)} - x_2^{(k)})\big], \tag{4.4}$$
--   the interval with these endpoints, open at $x_2^{(k)}$ and closed at the other end. Then, if the proximity property holds at iteration $k$, it holds at iteration $k + 1$.
--
--   Combined with Lemma 4.2 it shows that, once bracketed, the minimizer stays within a fixed multiple of the current diameter of the best vertex.
--
--   **Formalization Note** The orientation of $\operatorname{int}(\cdot,\cdot]$ is independent of the order of the endpoints, as on p. 124 of the paper.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 126, Lemma 4.3, (4.3), (4.4)

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem lemma_4_3 (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (hρχ : 1 ≤ ρ * χ) :
    ∀ k : ℕ, Proximity ρ χ γ xmin (run f ρ χ γ σ p0 k) →
      Proximity ρ χ γ xmin (run f ρ χ γ σ p0 (k + 1)) := by sorry

end NelderMeadLD.Conv1D
