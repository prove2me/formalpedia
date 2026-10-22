-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_smul_left
-- name    : JHolomorphic.HasWeakPartialsOn.smul_left
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T16:03:38.459861+00:00
-- url     : https://prove2.me/theorems/9177048b-9b2f-4f68-a36c-1b485b036b52
-- title:
--   Product rule for weak partial derivatives with a $C^1$ real factor
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $U\subseteq\mathbb{C}$ open, and let $w:\mathbb{C}\to E$ have weak partial derivatives $w_s,w_t$ on $U$, with $w,w_s,w_t$ integrable on every compact subset of $U$. If $\beta:\mathbb{C}\to\mathbb{R}$ is $C^1$, then $\beta w$ has weak partial derivatives on $U$ given by
--   $$\partial_s(\beta w)=(\partial_s\beta)\,w+\beta\,w_s,\qquad \partial_t(\beta w)=(\partial_t\beta)\,w+\beta\,w_t.$$
--   This is the weak Leibniz rule for multiplication by a smooth cutoff.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn`, tested against real $C^\infty$ functions with compact support in the given open set; the first weak partial is the derivative in the direction $1$ and the second in the direction $i$.
-- source:
--   Standard (weak derivatives and Lebesgue spaces).

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Product rule for weak partial derivatives with a real `C¹` factor: if `w` has weak partials
`wₛ`, `wₜ` on the open set `U`, all integrable on compact subsets of `U`, and `β : ℂ → ℝ` is `C¹`,
then `β • w` has weak partials `(∂ₛβ) w + β wₛ` and `(∂ₜβ) w + β wₜ` on `U`. -/
theorem HasWeakPartialsOn.smul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {β : ℂ → ℝ} (hβ : ContDiff ℝ 1 β)
    {w ws wt : ℂ → E} (hw : HasWeakPartialsOn U w ws wt)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn w K ∧ IntegrableOn ws K ∧ IntegrableOn wt K) :
    HasWeakPartialsOn U (fun z => β z • w z) (fun z => fderiv ℝ β z 1 • w z + β z • ws z)
      (fun z => fderiv ℝ β z Complex.I • w z + β z • wt z) := by
  sorry

end JHolomorphic
