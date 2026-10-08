-- Prove2me | Theorems.Thm_HarrisContact_Extinction_first_step_display
-- name    : HarrisContact.Extinction.first_step_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:53:50.536286+00:00
-- url     : https://prove2.me/theorems/3a50b52f-a0fd-4f0b-aafa-65fc22cfe1f4
-- title:
--   §7, display before Theorem 7.1, p. 981 — p_∞ = Σ r⁽ⁿ⁾(x, η) p_∞(η) ≤ p_∞ 𝓔_x|ξ_(n)|
-- statement:
--   Let $\{\xi_t\}$ be a subadditive contact process on $Z_d$: $d\ge1$, $\mu\ge0$, $\lambda_0=0$, $\lambda_1,\dots,\lambda_{2d}\ge0$, and $p_t(\xi\cup\eta)\le p_t(\xi)+p_t(\eta)$ for all finite $\xi,\eta$ and $t\ge0$ (5.3). Let $r^{(n)}$ be the $n$-step transition matrix of its imbedded jump chain. Writing $p_\infty$ for $p_\infty(\{x\})$, for every site $x$ and $n\ge1$,
--   $$p_\infty=\sum_{\eta\in\Xi_0}r^{(n)}(\{x\},\eta)\,p_\infty(\eta)\le p_\infty\sum_{\eta\in\Xi_0}r^{(n)}(\{x\},\eta)|\eta|.$$
--
--   The display is the paper's first-step identity and subadditivity bound. If the expected size of the embedded chain is less than $1$ for some $n$, it forces $p_\infty=0$.
--
--   **Formalization Note** Both clauses use the page's subadditivity hypothesis, a singleton initial set, and $n\ge1$. Values are in $[0,\infty]$.
-- source:
--   Harris (Ann. Probab. 2, 1974), §7, display preceding Theorem 7.1, p. 981 ("For subadditive processes … for each n = 1, 2, ⋯")

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- §7, display before Theorem 7.1 (p. 981): for a subadditive process and n ≥ 1,
p_∞(x) is harmonic for r^{(n)} and is at most p_∞(x) 𝓔_x |ξ_{(n)}|. -/
theorem first_step_display {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (h0 : lam 0 = 0) (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsubadd : ∀ t : ℝ, 0 ≤ t → ∀ ξ η : Config d,
      surv μ lam t (ξ ∪ η) ≤ surv μ lam t ξ + surv μ lam t η) :
    ∀ (n : ℕ), 1 ≤ n → ∀ x : Site d,
      (survInf μ lam {x} =
          ∑' η : Config d, ENNReal.ofReal (jumpPow μ lam n {x} η) * survInf μ lam η) ∧
        survInf μ lam {x} ≤
          survInf μ lam {x} *
            ∑' η : Config d, ENNReal.ofReal (jumpPow μ lam n {x} η) * (η.card : ℝ≥0∞) := by sorry

end HarrisContact.Extinction
