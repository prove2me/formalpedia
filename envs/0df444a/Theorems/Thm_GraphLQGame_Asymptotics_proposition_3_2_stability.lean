-- Prove2me | Theorems.Thm_GraphLQGame_Asymptotics_proposition_3_2_stability
-- name    : GraphLQGame.Asymptotics.proposition_3_2_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:26:44.539487+00:00
-- url     : https://prove2.me/theorems/34e9e517-36c7-4083-8f95-1638979e787a
-- title:
--   Proposition 3.2 (stability) — $Q'_{\mu_n}\to Q'_\mu$ and $f_{\mu_n}\to f_\mu$ uniformly on compacts of $\mathbb R_+$
-- statement:
--   Let $c>0$. For $\nu\in\mathcal P_{\mathrm{Lap}}$ (probability measures on $[-2,0]$ with mean $-1$) let $Q_\nu(x) = \exp\int_{[-2,0]}\log(1-x\lambda)\,\nu(d\lambda)$ and let $f_\nu:\mathbb R_+\to\mathbb R_+$ be the solution of
--   $$f_\nu'(t) = c\,Q_\nu'(f_\nu(t)),\quad t>0,\qquad f_\nu(0) = 0.$$
--   If $\mu_n$ is a sequence in $\mathcal P_{\mathrm{Lap}}$ converging weakly to $\mu\in\mathcal P_{\mathrm{Lap}}$, then for every compact $K\subseteq\mathbb R_+$
--   $$\sup_{x\in K}|Q'_{\mu_n}(x) - Q'_\mu(x)|\to 0\qquad\text{and}\qquad \sup_{t\in K}|f_{\mu_n}(t) - f_\mu(t)|\to0.$$
--
--   This stability of the ODE in its spectral input is what transfers convergence of $\mu_{G_n}$ to convergence of $f_{G_n}$, and from there of the equilibrium variances and values.
--
--   **Formalization Note** $f_{\mu_n}$ and $f_\mu$ are any solutions in the sense of Proposition 3.2 (existence and uniqueness are the first sentence of that proposition). $c>0$ is the paper's standing assumption.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Proposition 3.2, last sentence, p. 20

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium
import Definitions.Def_GraphLQGame_Asymptotics_Spectral
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace GraphLQGame.Asymptotics

/-- **Proposition 3.2**, last sentence (stability), Lacker–Soret, arXiv:2005.14102v2, §3, p. 20.

If `μ_k` is a sequence in `𝒫_Lap` converging weakly to `μ ∈ 𝒫_Lap`, then `Q'_{μ_k} → Q'_μ` and
`f_{μ_k} → f_μ` uniformly on compact subsets of `ℝ₊`, where `f_ν` is the solution on `ℝ₊` of
`f' = c Q'_ν(f)`, `f(0) = 0`.

Formalization Note: `f_{μ_k}` and `f_μ` are any solutions in the sense of Proposition 3.2
(`IsODESolRplus`); the first sentence of Proposition 3.2 gives existence and uniqueness. The
paper's convergence in `𝒫_Lap` (test functions continuous on `[−2, 0]`) is the same as weak
convergence against bounded continuous `h : ℝ → ℝ` for measures carried by `[−2, 0]`. `c > 0` is
the paper's standing assumption (§2.1). -/
theorem proposition_3_2_stability {c : ℝ} (hc : 0 < c) (μs : ℕ → Measure ℝ) (μ : Measure ℝ)
    (hμs : ∀ k, GraphLQGame.Equilibrium.IsPLap (μs k)) (hμ : GraphLQGame.Equilibrium.IsPLap μ) (hconv : WeakTendsto μs μ)
    (fs : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (hfs : ∀ k, GraphLQGame.Equilibrium.IsODESolRplus c (GraphLQGame.Equilibrium.Qmu (μs k)) (fs k))
    (hf : GraphLQGame.Equilibrium.IsODESolRplus c (GraphLQGame.Equilibrium.Qmu μ) f) :
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ici 0 →
      TendstoUniformlyOn (fun k => deriv (GraphLQGame.Equilibrium.Qmu (μs k))) (deriv (GraphLQGame.Equilibrium.Qmu μ)) atTop K ∧
      TendstoUniformlyOn fs f atTop K := by sorry

end GraphLQGame.Asymptotics
