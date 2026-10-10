-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_theorem_2_5
-- name    : GraphLQGame.Equilibrium.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:27:09.865323+00:00
-- url     : https://prove2.me/theorems/77b1f311-2c35-418a-8b8f-b46c970bf52e
-- title:
--   Theorem 2.5 — explicit Markovian Nash equilibrium on a finite transitive graph: Gaussian equilibrium law and average value (2.6)
-- statement:
--   Let $G$ be a finite transitive graph on $n$ vertices without isolated vertices, with random-walk Laplacian $L_G=D_G^{-1}A_G-I$, and let $T,\sigma,c>0$. Define $Q_G(x):=\det(I-xL_G)^{1/n}$ for $x\ge0$ (2.4). Then:
--
--   1. $Q_G:\mathbb R_+\to\mathbb R_+$ is well defined and continuously differentiable, and the ODE $f'_G(t)=cQ'_G(f_G(t))$, $f_G(0)=0$ has a unique solution $f_G:[0,T]\to\mathbb R_+$.
--   2. With $P_G(t):=-f'_G(T-t)L_G\big(I-f_G(T-t)L_G\big)^{-1}$ (2.5) and $\alpha^G_i(t,x):=-e_i^\top P_G(t)x$, the profile $(\alpha^G_i)_i$ is a Markovian Nash equilibrium of the game (2.1)–(2.3), for every non-random initial state $X^G(0)$.
--   3. For each $t\in(0,T]$, the equilibrium state $X^G(t)$ is Gaussian with mean $(I-f_G(T-t)L_G)(I-f_G(T)L_G)^{-1}X^G(0)$ and covariance
--   $$\sigma^2\big(I-f_G(T-t)L_G\big)^2\int_0^t\big(I-f_G(T-s)L_G\big)^{-2}\,ds .$$
--   4. The time-zero average value is
--   $$\mathrm{Val}(G):=\frac1n\sum_{v\in G}J^G_v\big((\alpha^G_i)_i\big)=\frac{|P_G(0)X^G(0)|^2}{2\,\mathrm{Tr}(P_G(0))}-\frac{\sigma^2}{2}\log\frac{\mathrm{Tr}(P_G(0))}{n\,f'_G(T)} .\qquad(2.6)$$
--
--   The theorem gives a semi-explicit equilibrium for a game on a graph with only nearest-neighbour interactions; its dependence on $G$ is entirely through the spectrum of $L_G$.
--
--   **Formalization Note** Vertices are `Fin n`. "Well defined" is $\det(I-xL_G)>0$ for $x\ge0$. Solutions of (2.1) are pathwise strong solutions on a probability space each solution carries; the existence of the equilibrium state process, which the paper presupposes, is part of the conclusion, and the law and value claims are made for every such solution. Costs are $[0,\infty]$-valued; their finiteness is asserted before converting to reals. $f'_G(T-t)$ is written $cQ'_G(f_G(T-t))$, its value by the ODE (so $f_G'(T)=cQ_G'(f_G(T))$). The equilibrium claims are stated for every $f$ solving the ODE on $[0,T]$, which by uniqueness is $f_G$. The covariance integral is entrywise and $|y|^2=\sum_ky_k^2$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Theorem 2.5, §2.2, p. 6

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GraphLQGame.Equilibrium

open EthierKurtz

/-- Lacker–Soret, arXiv:2005.14102v2, Theorem 2.5 (Characterization of equilibrium on transitive
graphs), §2.2, p. 6. Let `G` be a finite transitive graph on `n` vertices without isolated
vertices, `T, σ, c > 0`. Then:
* `Q_G(x) = det(I − xL_G)^{1/n}` is well defined (`det(I − xL_G) > 0`), `ℝ₊`-valued and
  continuously differentiable on `ℝ₊`;
* the ODE `f'(t) = c Q_G'(f(t))`, `f(0) = 0` has a unique solution `f_G : [0, T] → ℝ₊`;
* for this solution and every non-random initial state `X(0) = x0`, the feedback
  `α_i^G(t, x) = −e_iᵀ P_G(t) x`, `P_G(t) = −f_G'(T − t) L_G (I − f_G(T − t) L_G)⁻¹` (2.5), is a
  Markovian Nash equilibrium; the equilibrium state equation has a solution; for every solution
  and every `t ∈ (0, T]`, `X(t)` is Gaussian with mean `(I − f_G(T − t)L_G)(I − f_G(T)L_G)⁻¹ x0` and
  covariance `σ² (I − f_G(T − t)L_G)² ∫_0^t (I − f_G(T − s)L_G)⁻² ds`; every player's cost is finite;
  and the average value is (2.6):
  `Val(G) = (1/n) Σ_v J_v^G = |P_G(0) x0|² / (2 Tr P_G(0)) − (σ²/2) log(Tr P_G(0) / (n f_G'(T)))`.

Formalization Note: vertices are `Fin n`; solutions of (2.1) are pathwise strong solutions on a
probability space each solution carries (`StateSol`), and costs are `ℝ≥0∞`-valued lower integrals,
converted to reals only after their finiteness is asserted. The existence of a solution of the
equilibrium state equation, which the paper presupposes, is part of the conclusion. `f_G'(T − t)` is
written `c Q_G'(f_G(T − t))`, its value by the ODE (so `f_G'(T) = c Q_G'(f_G(T))`). The claims for
`α^G` are made for every `f` solving the ODE on `[0, T]`, which by uniqueness is `f_G`. The
covariance integral is entrywise; `|y|²` is `Σ_k y_k²`. -/
theorem theorem_2_5 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hT : IsTransitive G) (hN : NoIsolated G) (c σ T : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (hTpos : 0 < T) :
    ((∀ x : ℝ, 0 ≤ x → 0 < Matrix.det (1 - x • lap G)) ∧
        (∀ x : ℝ, 0 ≤ x → 0 ≤ QG G x) ∧ ContDiffOn ℝ 1 (QG G) (Set.Ici 0)) ∧
      ((∃ f : ℝ → ℝ, IsFSol c T (QG G) f) ∧
        ∀ f g : ℝ → ℝ, IsFSol c T (QG G) f → IsFSol c T (QG G) g → Set.EqOn f g (Set.Icc 0 T)) ∧
      ∀ f : ℝ → ℝ, IsFSol c T (QG G) f → ∀ x0 : SDEState n,
        IsMarkovNash G c T σ x0 0 (alphaG G c T f) ∧
        Nonempty (StateSol n T σ x0 (alphaG G c T f)) ∧
        ∀ S : StateSol n T σ x0 (alphaG G c T f),
          (∀ t ∈ Set.Ioc (0 : ℝ) T,
            S.P.map (S.X t) =
              multivariateGaussian
                (WithLp.toLp 2 (((1 - f (T - t) • lap G) * (1 - f T • lap G)⁻¹).mulVec
                  (fun j => x0 j)) : SDEState n)
                (σ ^ 2 • ((1 - f (T - t) • lap G) ^ 2 *
                  Matrix.of fun i j => ∫ s in (0 : ℝ)..t, (((1 - f (T - s) • lap G)⁻¹) ^ 2) i j))) ∧
          (∀ v : Fin n, cost G c T S v ≠ ⊤) ∧
          (n : ℝ)⁻¹ * ∑ v : Fin n, (cost G c T S v).toReal =
            (∑ k : Fin n, ((PG G c T f 0).mulVec (fun j => x0 j) k) ^ 2) /
                (2 * (PG G c T f 0).trace) -
              σ ^ 2 / 2 * Real.log ((PG G c T f 0).trace / (n * (c * deriv (QG G) (f T)))) := by sorry

end GraphLQGame.Equilibrium
