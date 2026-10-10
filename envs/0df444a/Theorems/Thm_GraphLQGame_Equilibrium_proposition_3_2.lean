-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_proposition_3_2
-- name    : GraphLQGame.Equilibrium.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:26:25.611826+00:00
-- url     : https://prove2.me/theorems/dcfe6428-483f-46af-8e7a-1d5ddd22f32e
-- title:
--   Proposition 3.2 (first two sentences) — well-posedness of $f_\mu' = cQ_\mu'(f_\mu)$, $f_\mu(0)=0$ on $\mathbb R_+$ and the bounds on $f_\mu$
-- statement:
--   Let $\mu\in\mathcal P_{\mathrm{Lap}}$ and $c>0$. There is a unique continuous function $f_\mu:\mathbb R_+\to\mathbb R_+$, continuously differentiable on $(0,\infty)$, satisfying
--   $$f'_\mu(t)=cQ'_\mu(f_\mu(t)),\quad t>0,\qquad f_\mu(0)=0 .$$
--   Moreover, for all $t\ge0$,
--   $$0\le f_\mu(t)\le ct,\qquad f_\mu(t)\ge ct-\big(\tfrac12c^2t^2+\tfrac16c^3t^3\big)\mathrm{Var}(\mu).$$
--
--   With $\mu=\mu_G$ this yields the function $f_G$ of Theorem 2.5.
--
--   **Formalization Note** Uniqueness is agreement on $[0,\infty)$; values off $\mathbb R_+$ are unconstrained. $c>0$ is the paper's standing assumption (§2.1). The third sentence of the proposition (stability in $\mu$) is not part of this item.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Proposition 3.2, first two sentences, p. 20

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Spectral

open MeasureTheory

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, Proposition 3.2 (first two sentences), p. 20. Let
`µ ∈ 𝒫_Lap` and `c > 0`. There is a unique continuous `f_µ : ℝ₊ → ℝ₊`, continuously
differentiable on `(0, ∞)`, with `f'_µ(t) = c Q'_µ(f_µ(t))` for `t > 0` and `f_µ(0) = 0`. Moreover
`0 ≤ f_µ(t) ≤ ct` and `f_µ(t) ≥ ct − (c²t²/2 + c³t³/6) Var(µ)` for `t ≥ 0`.

Formalization Note: uniqueness is agreement on `ℝ₊ = [0, ∞)` (values off `ℝ₊` are
unconstrained); `c > 0` is the paper's standing assumption (§2.1). -/
theorem proposition_3_2 (μ : Measure ℝ) (hμ : IsPLap μ) (c : ℝ) (hc : 0 < c) :
    (∃ f : ℝ → ℝ, IsODESolRplus c (Qmu μ) f) ∧
      (∀ f g : ℝ → ℝ, IsODESolRplus c (Qmu μ) f → IsODESolRplus c (Qmu μ) g →
        Set.EqOn f g (Set.Ici 0)) ∧
      (∀ f : ℝ → ℝ, IsODESolRplus c (Qmu μ) f → ∀ t : ℝ, 0 ≤ t →
        0 ≤ f t ∧ f t ≤ c * t ∧
          c * t - (1 / 2 * c ^ 2 * t ^ 2 + 1 / 6 * c ^ 3 * t ^ 3) * VarMu μ ≤ f t) := by sorry

end GraphLQGame.Equilibrium
