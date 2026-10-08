-- Prove2me | Theorems.Thm_NumStochOpt_Nonstationary_lemma_p155_conditions_1_2a
-- name    : NumStochOpt.Nonstationary.lemma_p155_conditions_1_2a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:32:57.386409+00:00
-- url     : https://prove2.me/theorems/90554122-7f05-4eca-a076-6af259b7182f
-- title:
--   p. 155 — conditions (1) and (2)(a) of Theorem 6.4 hold for the method (6.41)
-- statement:
--   Let $X \subseteq \mathbb R^n$ be a nonempty convex compact set, let $\rho_s \ge 0$ with $\rho_s \to 0$, let $\|g_s\| \le C$ for all $s$, and let $x^{s+1} = \pi_X[x^s - \rho_s g_s]$ for $s = 0, 1, \dots$ (6.41). Then
--
--   1. there is a compact set $K \subseteq \mathbb R^n$ with $x^s \in K$ for all $s$ (condition (1) of Theorem 6.4), and
--   2. the steps vanish:
--   $$
--   \|x^{s+1} - x^s\| \to 0 \quad (s \to \infty).
--   $$
--
--   The second item gives condition (2)(a) of Theorem 6.4 for every subsequence and every choice of the set $X^*$. Together with the next milestone it verifies all hypotheses of Theorem 6.4 for the iteration (6.41).
--
--   **Formalization Note** The book states "The conditions 1, 2(a) of Theorem 6.4 are fulfilled"; the Lean statement gives the whole-sequence form of (2)(a), which implies the subsequence form. $K$ can be taken as $X \cup \{x^0\}$; the starting point $x^0$ need not lie in $X$.
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 155, proof of Theorem 6.3, first sentence

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod

open Filter Topology

namespace NumStochOpt.Nonstationary

/-- Proof of Theorem 6.3, p. 155: "The conditions 1, 2(a) of Theorem 6.4 are fulfilled." For
the iteration (6.41) `x^{s+1} = π_X[x^s - ρ_s g_s]` on a convex compact `X ⊆ ℝⁿ` with
`ρ_s ≥ 0`, `ρ_s → 0` and `‖g_s‖ ≤ C`: the whole sequence lies in a compact set (condition (1))
and `‖x^{s+1} - x^s‖ → 0` (which gives condition (2)(a) for every subsequence). -/
theorem lemma_p155_conditions_1_2a {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXconv : Convex ℝ X) (hXcpt : IsCompact X)
    (hXne : X.Nonempty)
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C : ℝ)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • g s))
    (hρnn : ∀ s, 0 ≤ ρ s) (hρ0 : Tendsto ρ atTop (𝓝 0)) (hbound : ∀ s, ‖g s‖ ≤ C) :
    (∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ ∀ s, x s ∈ K) ∧
      Tendsto (fun s => ‖x (s + 1) - x s‖) atTop (𝓝 0) := by sorry

end NumStochOpt.Nonstationary
