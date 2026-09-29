-- Prove2me | Theorems.Thm_LogRegretOCO_EWOO_shrunk_set_bound
-- name    : LogRegretOCO.EWOO.shrunk_set_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:44:58.622057+00:00
-- url     : https://prove2.me/theorems/2f984a20-dae9-42ea-9564-7ed06b7d2201
-- title:
--   §3.4 (p. 187): on S, h_t(x) ≥ (T/(T+1)) h_t(x*) and ∏ h_τ(x) ≥ (T/(T+1))^T ∏ h_τ(x*) ≥ (1/e) ∏ h_τ(x*)
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be convex, let $\alpha \in \mathbb{R}$, and let $f_1, f_2, \dots : \mathbb{R}^n \to \mathbb{R}$ be $\alpha$-exp-concave on $P$; write $h_\tau(x) = e^{-\alpha f_\tau(x)}$. Fix $x^* \in P$ and $T \in \mathbb{N}$, and let
--
--   $$
--   S = \Bigl\{ \tfrac{T}{T+1}\, x^* + \tfrac{1}{T+1}\, y \;:\; y \in P \Bigr\}.
--   $$
--
--   Then:
--
--   1. for every $t$ and every $x \in S$, $\; h_t(x) \ge \frac{T}{T+1}\, h_t(x^*)$;
--   2. for every $x \in S$,
--   $$
--   \prod_{\tau=1}^{T} h_\tau(x) \;\ge\; \Bigl(\frac{T}{T+1}\Bigr)^{T} \prod_{\tau=1}^{T} h_\tau(x^*) \;\ge\; \frac{1}{e} \prod_{\tau=1}^{T} h_\tau(x^*).
--   $$
--
--   The first part uses only concavity and nonnegativity of $h_t$; the second multiplies over rounds and uses $(1 + 1/T)^T \le e$. Applied with $x^*$ a minimizer of the cumulative cost, it says that every point of $S$ is almost as good as $x^*$ for the product of the $h_\tau$.
--
--   **Formalization Note** The paper takes $x^* \in \arg\min_{x \in P} \sum_{t=1}^T f_t(x)$; the inequalities hold for every $x^* \in P$, which is what is stated. The paper's set-builder "$S = \{x \in S \mid \dots\}$" is read as the set of all such $x$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 187, §3.4, proof of Theorem 7, displays defining S and bounding h_t and ∏ h_τ on S

import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_shrunkSet

namespace LogRegretOCO.EWOO

/-- §3.4, displays on p. 187 (Hazan–Agarwal–Kale 2007): on the shrunken set
`S = {T/(T+1) x* + 1/(T+1) y : y ∈ P}`, each `h_t = exp(-α f_t)` satisfies
`h_t(x) ≥ T/(T+1) h_t(x*)`, hence
`∏_{τ=1}^T h_τ(x) ≥ (T/(T+1))^T ∏_{τ=1}^T h_τ(x*) ≥ (1/e) ∏_{τ=1}^T h_τ(x*)`. -/
theorem shrunk_set_bound (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ P) (T : ℕ) :
    (∀ t, ∀ x ∈ shrunkSet P xstar T,
        ((T : ℝ) / ((T : ℝ) + 1)) * Real.exp (-α * f t xstar) ≤ Real.exp (-α * f t x)) ∧
    (∀ x ∈ shrunkSet P xstar T,
        ((T : ℝ) / ((T : ℝ) + 1)) ^ T * ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
            ≤ ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ x) ∧
          (1 / Real.exp 1) * ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
            ≤ ((T : ℝ) / ((T : ℝ) + 1)) ^ T *
                ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)) := by sorry

end LogRegretOCO.EWOO
