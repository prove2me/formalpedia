-- Prove2me | Theorems.Thm_NumStochOpt_Nonstationary_lemma_p155_distance_recursion
-- name    : NumStochOpt.Nonstationary.lemma_p155_distance_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:32:24.503305+00:00
-- url     : https://prove2.me/theorems/c6615783-1ad2-4960-8dd3-a311ca375423
-- title:
--   p. 155 — one-step recursion $V(x^{s+1}) \le V(x^s) + 2\rho_s\langle g_s, x^*(s) - x^s\rangle + \rho_s^2\|g_s\|^2$
-- statement:
--   Let $X \subseteq \mathbb R^n$ be closed and convex, let $f : \mathbb R^n \to \mathbb R$, and let $X^*$ be the set of minimizers of $f$ over $X$. Put
--   $$
--   V(x) = \min_{x^* \in X^*} \|x^* - x\|^2 ,
--   $$
--   the squared distance from $x$ to $X^*$. Let $x^s, g_s \in \mathbb R^n$, $\rho_s \in \mathbb R$, and $x^{s+1} = \pi_X[x^s - \rho_s g_s]$. If $x^*(s) \in X^*$ is a point of $X^*$ nearest to $x^s$, i.e. $\|x^*(s) - x^s\|^2 = V(x^s)$, then
--
--   $$
--   V(x^{s+1}) \le V(x^s) + 2\rho_s \langle g_s, x^*(s) - x^s\rangle + \rho_s^2 \|g_s\|^2 .
--   $$
--
--   This is the first estimate of the proof of Theorem 6.3: it measures how one step of the projected subgradient method (6.41) changes the distance to the optimal set of the limit problem.
--
--   **Formalization Note** $V(x)$ is written as the square of `Metric.infDist x X*`. The book's chain prints "$= V(x^s) + 2\rho_s\langle\cdot\rangle + \rho_s^2\|\cdot\|^2$" after $\|x^*(s) - x^{s+1}\|^2$; the relation there is an inequality, and the conclusion stated is the resulting inequality between its two ends. The nearest point $x^*(s)$ is taken as a hypothesis (it exists whenever $X^*$ is nonempty and compact).
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 155, proof of Theorem 6.3, unnumbered display

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod

open scoped RealInnerProductSpace

namespace NumStochOpt.Nonstationary

/-- Proof of Theorem 6.3, p. 155 (unnumbered display). Let `X ⊆ ℝⁿ` be closed and convex,
`X* = NumStochOpt.QuasiFejer.optimalSet f X` the set of minimizers of `f` over `X`, and `V(x) = min_{x* ∈ X*} ‖x* - x‖²`
(written `(infDist x X*)²`). If `x^{s+1} = π_X[x^s - ρ_s g_s]` and `x*(s) ∈ X*` is a point of
`X*` nearest to `x^s`, then
`V(x^{s+1}) ≤ V(x^s) + 2ρ_s⟨g_s, x*(s) - x^s⟩ + ρ_s²‖g_s‖²`.
The book prints `=` before `V(x^s) + …`; the relation is `≤` (nonexpansiveness of `π_X`). -/
theorem lemma_p155_distance_recursion {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hXclosed : IsClosed X) (hXconv : Convex ℝ X)
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (s : ℕ)
    (hrec : x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • g s))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ NumStochOpt.QuasiFejer.optimalSet f X)
    (hnear : ‖xstar - x s‖ = Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X)) :
    Metric.infDist (x (s + 1)) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 ≤
      Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 + 2 * ρ s * ⟪g s, xstar - x s⟫
        + ρ s ^ 2 * ‖g s‖ ^ 2 := by sorry

end NumStochOpt.Nonstationary
