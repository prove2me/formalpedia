-- Prove2me | Theorems.Thm_IsodiamVar_Simplex_theorem_1_7
-- name    : IsodiamVar.Simplex.theorem_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:12.031828+00:00
-- url     : https://prove2.me/theorems/6fa8356f-5b57-495e-8960-304e94ba2a2f
-- title:
--   Theorem 1.7 — maximizing generalized variance
-- statement:
--   Let $K\subseteq\mathbb R^n$ be nonempty and compact, and let $V:\mathbb R^n\to[0,\infty)$ be convex and coercive. Let $\lambda\ge0$ be the smallest radius level for which some translate $K+z$ lies in $\{x:V(x)\le\lambda\}$. Then
--
--   $$
--   \lambda=\sup_{\mu\in\mathcal P(K)}\operatorname{Var}_V(\mu).
--   $$
--
--   A measure $\mu\in\mathcal P(K)$ attains this supremum exactly when some center $z_*$ minimizes $z\mapsto\int V(x-z)\,d\mu(x)$ and $V(x-z_*)=\lambda$ on the support of $\mu$. This connects the maximizing measure to a tight enclosing level set.
--
--   **Formalization Note** Nonemptiness of $K$ is explicit. The support condition follows the proof on p. 12; the printed set $V^{-1}(\lambda)-z_*$ has the opposite translation sign.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 5, Theorem 1.7; p. 12, proof of Theorem 1.7

import Mathlib
import Definitions.Def_IsodiamVar_Simplex_Defs

open MeasureTheory

namespace IsodiamVar.Simplex

/-- Theorem 1.7: generalized variance and its maximizing measures. -/
theorem theorem_1_7 {n : ℕ} (K : Set (E n)) (hK : IsCompact K) (hKne : K.Nonempty)
    (V : E n → ℝ) (hV0 : ∀ x, 0 ≤ V x) (hVconv : ConvexOn ℝ Set.univ V)
    (hVcoer : Coercive V) (lam : ℝ)
    (hlam : IsLeast {t : ℝ | 0 ≤ t ∧ ∃ z : E n, ∀ x ∈ K, V (x + z) ≤ t} lam) :
    IsLUB {s : ℝ | ∃ μ : Measure (E n), InP K μ ∧ s = varV V μ} lam ∧
      ∀ μ : Measure (E n), InP K μ →
        (varV V μ = lam ↔
          ∃ zs : E n, IsMinOn (fun z => ∫ x, V (x - z) ∂μ) Set.univ zs ∧
            μ.support ⊆ {x | V (x - zs) = lam}) := by sorry

end IsodiamVar.Simplex
