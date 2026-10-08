-- Prove2me | Theorems.Thm_NelderMeadLD_Conv1D_lemma_4_2
-- name    : NelderMeadLD.Conv1D.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:03.633979+00:00
-- url     : https://prove2.me/theorems/5afc0c82-c329-4daf-81d6-3befc464c672
-- title:
--   Lemma 4.2, p. 125 — with ρχ ≥ 1 the minimizer is eventually bracketed by x₂ and x_e (without the printed bound on K)
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ be strictly convex with bounded level sets $\{x : f(x) \le \mu\}$, and let $x_{\min}$ be its minimizer. Let the parameters satisfy (2.1) and in addition $\rho\chi \ge 1$, and let $\Delta_k = (x_1^{(k)}, x_2^{(k)})$ be the one-dimensional Nelder–Mead run from a nondegenerate, ordered initial interval $\Delta_0$. Write $x_e^{(k)} = x_1^{(k)} + \rho\chi(x_1^{(k)} - x_2^{(k)})$ for the expansion point and $f_i^{(k)} = f(x_i^{(k)})$, $f_e^{(k)} = f(x_e^{(k)})$.
--
--   Then there is a smallest integer $K \ge 0$ such that
--   $$f_2^{(K)} \ge f_1^{(K)} \quad\text{and}\quad f_1^{(K)} \le f_e^{(K)},$$
--   and for this $K$ the minimizer is **bracketed** by $x_2^{(K)}$ and $x_e^{(K)}$: $x_{\min} \in \operatorname{int}(x_2^{(K)}, x_e^{(K)})$, the open interval with these endpoints.
--
--   The lemma is the first step of the convergence proof: within finitely many iterations the method finds an interval of uncertainty containing the minimizer.
--
--   **Formalization Note** The printed lemma also asserts $K \le |x_{\min} - x_1^{(0)}| / \operatorname{diam}(\Delta_0)$. That bound is false: for $f(x) = (x-5)^2$, $\Delta_0 = (3, 0)$, $\rho = 1$, $\chi = 1.1$, the bound is $2/3$, but $f_1^{(0)} = 4 > f_e^{(0)} = f(6.3) = 1.69$, so $K \ge 1$. The bound is not stated here and no substitute bound is invented; Theorem 4.1 uses only the existence of $K$. "Smallest" is stated as: the condition fails at every $j < K$. The coefficients $\gamma, \sigma$ are constrained by the standing conditions (2.1).
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 125, Lemma 4.2, (4.2) (printed bound on K omitted: false)

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem lemma_4_2 (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (hρχ : 1 ≤ ρ * χ) :
    ∃ K : ℕ, Bracketed ρ χ f (run f ρ χ γ σ p0 K) ∧
      (∀ j < K, ¬ Bracketed ρ χ f (run f ρ χ γ σ p0 j)) ∧
      min (run f ρ χ γ σ p0 K).2 (xe ρ χ (run f ρ χ γ σ p0 K)) < xmin ∧
      xmin < max (run f ρ χ γ σ p0 K).2 (xe ρ χ (run f ρ χ γ σ p0 K)) := by sorry

end NelderMeadLD.Conv1D
