-- Prove2me | Theorems.Thm_NumStochOpt_Nonstationary_lemma_p156_step_bound
-- name    : NumStochOpt.Nonstationary.lemma_p156_step_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:32:35.88276+00:00
-- url     : https://prove2.me/theorems/077e1ad5-9d32-4086-aa30-1b51aa358000
-- title:
--   p. 156 — $\|x^{b} - x^{a}\| \le \sum_{s=a}^{b-1}\|x^{s+1} - x^s\| \le C\sum_{s=a}^{b-1}\rho_s$
-- statement:
--   Let $X \subseteq \mathbb R^n$ be a convex compact set, $\rho_s \ge 0$, and let $g_s \in \mathbb R^n$ satisfy $\|g_s\| \le C$ for all $s$. Let $(x^s)$ satisfy the projected subgradient recursion (6.41)
--   $$
--   x^{s+1} = \pi_X[x^s - \rho_s g_s], \qquad s = 0, 1, \dots
--   $$
--   If $a \le b$ and $x^a \in X$, then
--
--   $$
--   \|x^b - x^a\| \;\le\; \sum_{s=a}^{b-1} \|x^{s+1} - x^s\| \;\le\; C \sum_{s=a}^{b-1} \rho_s .
--   $$
--
--   In the proof of Theorem 6.3 this bounds the distance travelled between the index $s_k$ of a subsequence and the exit time $\tau_k$, which converts the decrease of $V$ into a decrease proportional to $\varepsilon$.
--
--   **Formalization Note** The book writes "where $C$ is a constant"; the proof yields $C$ = the constant of hypothesis (d) of Theorem 6.3, $\|g_s\| \le C$. The hypothesis $x^a \in X$ holds for every $a \ge 1$ (all iterates after the first are projections onto $X$); in the book $a = s_k$ is large. $\rho_s \ge 0$ is the step-size convention of the chapter, not printed in Theorem 6.3.
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 156, proof of Theorem 6.3, unnumbered display

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod

namespace NumStochOpt.Nonstationary

/-- Proof of Theorem 6.3, p. 156 (unnumbered display): "in view of the properties of `π_X`",
`‖x^τ - x^a‖ ≤ ∑_{s=a}^{τ-1} ‖x^{s+1} - x^s‖ ≤ C ∑_{s=a}^{τ-1} ρ_s` along the iteration (6.41)
`x^{s+1} = π_X[x^s - ρ_s g_s]`, where `C` is the bound of hypothesis (d), `‖g_s‖ ≤ C`, and
`x^a ∈ X` (which holds for every `a ≥ 1`). -/
theorem lemma_p156_step_bound {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXconv : Convex ℝ X) (hXcpt : IsCompact X)
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C : ℝ)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • g s))
    (hρnn : ∀ s, 0 ≤ ρ s) (hbound : ∀ s, ‖g s‖ ≤ C)
    (a b : ℕ) (hab : a ≤ b) (hxa : x a ∈ X) :
    ‖x b - x a‖ ≤ ∑ s ∈ Finset.Ico a b, ‖x (s + 1) - x s‖ ∧
      ∑ s ∈ Finset.Ico a b, ‖x (s + 1) - x s‖ ≤ C * ∑ s ∈ Finset.Ico a b, ρ s := by sorry

end NumStochOpt.Nonstationary
