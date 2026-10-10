-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_proposition_3_1
-- name    : GraphLQGame.Equilibrium.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:26:32.587306+00:00
-- url     : https://prove2.me/theorems/7b460384-8e0c-49e9-9425-24ed11a49365
-- title:
--   Proposition 3.1 — bounds $1\le Q_\mu\le 1+x$, $0<Q_\mu'\le1$, $-4\le Q_\mu''\le0$, $Q_\mu'\ge 1-(x+x^2/2)\mathrm{Var}(\mu)$
-- statement:
--   Let $\mu\in\mathcal P_{\mathrm{Lap}}$, a probability measure on $[-2,0]$ with mean $-1$, and $Q_\mu(x)=\exp\int_{[-2,0]}\log(1-x\lambda)\,\mu(d\lambda)$. For all $x\ge0$,
--   $$1\le Q_\mu(x)\le1+x,\qquad 0<Q'_\mu(x)\le1,\qquad -4\le Q''_\mu(x)\le0,$$
--   and
--   $$Q'_\mu(x)\ge1-\big(x+\tfrac12x^2\big)\mathrm{Var}(\mu),\qquad \mathrm{Var}(\mu)=\int_{[-2,0]}(\lambda+1)^2\,\mu(d\lambda).$$
--
--   These bounds give the Lipschitz property of $Q'_\mu$ used for well-posedness of the ODE.
--
--   **Formalization Note** $Q'_\mu$ and $Q''_\mu$ are `deriv` and iterated `deriv` of the function on $\mathbb R$; $Q_\mu$ is smooth on $x>-1/2$, so at $x\ge0$ these are the true derivatives.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Proposition 3.1, p. 19

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Spectral

open MeasureTheory

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, Proposition 3.1, p. 19. For each `µ ∈ 𝒫_Lap`, for all
`x ≥ 0`:
`1 ≤ Q_µ(x) ≤ 1 + x`, `0 < Q'_µ(x) ≤ 1`, `−4 ≤ Q''_µ(x) ≤ 0`, and
`Q'_µ(x) ≥ 1 − (x + x²/2) Var(µ)`, `Var(µ) = ∫_{[−2,0]} (λ + 1)² µ(dλ)`.

Formalization Note: `Q'_µ`, `Q''_µ` are `deriv (Qmu µ)` and `deriv (deriv (Qmu µ))`; `Q_µ` is smooth
on the open set `x > −1/2`, so these are the true derivatives at every `x ≥ 0`. -/
theorem proposition_3_1 (μ : Measure ℝ) (hμ : IsPLap μ) (x : ℝ) (hx : 0 ≤ x) :
    1 ≤ Qmu μ x ∧ Qmu μ x ≤ 1 + x ∧
      0 < deriv (Qmu μ) x ∧ deriv (Qmu μ) x ≤ 1 ∧
      -4 ≤ deriv (deriv (Qmu μ)) x ∧ deriv (deriv (Qmu μ)) x ≤ 0 ∧
      1 - (x + 1 / 2 * x ^ 2) * VarMu μ ≤ deriv (Qmu μ) x := by sorry

end GraphLQGame.Equilibrium
