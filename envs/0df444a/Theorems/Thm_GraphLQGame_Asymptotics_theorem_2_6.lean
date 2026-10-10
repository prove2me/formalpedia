-- Prove2me | Theorems.Thm_GraphLQGame_Asymptotics_theorem_2_6
-- name    : GraphLQGame.Asymptotics.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:26:44.824109+00:00
-- url     : https://prove2.me/theorems/2ed96235-37eb-4297-98bf-cb43dec9c235
-- title:
--   Theorem 2.6 — large-scale asymptotics of the equilibrium on transitive graphs whose Laplacian spectra converge
-- statement:
--   Let $(G_n)$ be a sequence of finite transitive graphs without isolated vertices with $|G_n|\to\infty$, and let $T,\sigma,c>0$. Let $\boldsymbol X^{G_n}$ be the equilibrium state process of Theorem 2.5 (the solution of (2.1) under the Nash feedback $\alpha^{G_n}$) started from $\boldsymbol X^{G_n}(0) = 0$. Suppose the empirical eigenvalue distributions $\mu_{G_n}$ of the Laplacians converge weakly to a probability measure $\mu$, and let
--   $$Q_\mu(x) := \exp\int_{[-2,0]}\log(1-x\lambda)\,\mu(d\lambda).$$
--   Then:
--
--   1. There is a unique solution $f_\mu:[0,T]\to\mathbb R_+$ of
--   $$f_\mu'(t) = c\,Q_\mu'(f_\mu(t)),\qquad f_\mu(0) = 0.\qquad(2.10)$$
--   2. For every vertex sequence $k_n\in G_n$ and every $t\in[0,T]$, the law of $X^{G_n}_{k_n}(t)$ converges weakly to the centered Gaussian law with variance
--   $$V_\mu(t) = \sigma^2\int_0^t\int_{[-2,0]}\Big(\frac{1-\lambda f_\mu(T-t)}{1-\lambda f_\mu(T-s)}\Big)^2\mu(d\lambda)\,ds.\qquad(2.11)$$
--   3. For every $t\in[0,T]$, the random empirical measure $\frac1{|G_n|}\sum_{i\in G_n}\delta_{X^{G_n}_i(t)}$ converges weakly in probability to $\mathcal N(0,V_\mu(t))$.
--   4. The time-zero values converge:
--   $$\lim_{n\to\infty}\mathrm{Val}(G_n) = -\frac{\sigma^2}{2}\log\int_{[-2,0]}\frac{-\lambda}{1-\lambda f_\mu(T)}\,\mu(d\lambda).\qquad(2.12)$$
--
--   The limit of the equilibrium depends on the graphs only through the limit $\mu$ of their Laplacian spectra; the dense case $\mu = \delta_{-1}$ recovers the mean field game.
--
--   **Formalization Note** Vertices are `Fin n`. Every state process carries its own probability space, so (2) and (3) are statements about laws. Weak convergence is tested against all bounded continuous $h$; "weakly in probability" means that $\int h\,dm^{G_n}(t)\to\int h\,d\mathcal N(0,V_\mu(t))$ in probability for every bounded continuous $h$, the notion the paper's proof establishes. The statement holds for every solution $f_{G_n}$ of the graph ODE and every equilibrium state process, and it also asserts that these exist, so it is not vacuous. Costs are $[0,\infty]$-valued; (4) asserts their finiteness before converting to reals. Uniqueness in (1) is uniqueness on $[0,T]$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §2.3, Theorem 2.6, p. 8; proof in §7.1, pp. 37–39

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

open EthierKurtz

/-- **Theorem 2.6** (Large-scale asymptotics on transitive graphs), Lacker–Soret,
arXiv:2005.14102v2, §2.3, p. 8.

Let `G k` be finite transitive graphs on `Fin (N k)` without isolated vertices, `N k → ∞`, and let
the empirical eigenvalue distributions `μ_{G_k}` converge weakly to a probability measure `μ`.
Then (1) the ODE (2.10) for `Q_μ` has a solution on `[0, T]`, unique on `[0, T]`; and, for every
such solution `f`, every choice of the graph ODE solutions `f_{G_k}` and every choice of
equilibrium state processes `X^{G_k}` (solutions of (2.1) under `α^{G_k}` from `X(0) = 0`), which
exist: (2) the law of `X^{G_k}_{k_n}(t)` converges weakly to `𝒩(0, V_μ(t))` for any vertex sequence;
(3) the empirical measure `(1/|G_k|) Σ_i δ_{X_i(t)}` converges weakly in probability to
`𝒩(0, V_μ(t))`; (4) the costs are finite and `Val(G_k) → −(σ²/2) log ∫_{[−2,0]} −λ/(1 − λ f(T)) μ(dλ)`.

Formalization Note: vertices `{1, …, n}` are `Fin n`; each state process carries its own
probability space, so (2) and (3) are statements about laws; weak convergence is tested against all
bounded continuous `h : ℝ → ℝ`; weak convergence in probability is convergence in probability of
`∫ h dm` for every bounded continuous `h` (the notion of p. 38); `gaussianReal` takes its variance in
`ℝ≥0`, and `V_μ(t) ≥ 0`; costs are `ℝ≥0∞` lower integrals, converted to reals after finiteness. The
existence of `f_{G_k}` and of the state processes is asserted to rule out a vacuous statement. -/
theorem theorem_2_6 {N : ℕ → ℕ} (G : ∀ k, SimpleGraph (Fin (N k)))
    [∀ k, DecidableRel (G k).Adj] {T σ c : ℝ} (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c)
    (htrans : ∀ k, GraphLQGame.Equilibrium.IsTransitive (G k)) (hiso : ∀ k, GraphLQGame.Equilibrium.NoIsolated (G k))
    (hN : Tendsto N atTop atTop) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hconv : WeakTendsto (fun k => GraphLQGame.Equilibrium.specMeasure (G k)) μ) :
    -- (1) existence and uniqueness of `f_μ` on `[0, T]`
    ((∃ f : ℝ → ℝ, GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.Qmu μ) f) ∧
      ∀ f g : ℝ → ℝ, GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.Qmu μ) f → GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.Qmu μ) g → Set.EqOn f g (Set.Icc 0 T)) ∧
    -- the equilibrium objects of Theorem 2.5 exist
    (∀ k, ∃ f : ℝ → ℝ, GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.QG (G k)) f) ∧
    ∀ (f : ℝ → ℝ), GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.Qmu μ) f →
    ∀ (fk : ℕ → ℝ → ℝ), (∀ k, GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.QG (G k)) (fk k)) →
      (∀ k, Nonempty (GraphLQGame.Equilibrium.StateSol (N k) T σ 0 (GraphLQGame.Equilibrium.alphaG (G k) c T (fk k)))) ∧
      ∀ (S : ∀ k, GraphLQGame.Equilibrium.StateSol (N k) T σ 0 (GraphLQGame.Equilibrium.alphaG (G k) c T (fk k))),
        -- (2) one player's law
        (∀ (kn : ∀ k, Fin (N k)), ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ h : ℝ →ᵇ ℝ,
          Tendsto (fun k => ∫ ω, h ((S k).X t ω (kn k)) ∂(S k).P) atTop
            (𝓝 (∫ x, h x ∂(gaussianReal 0 (Vmu σ c T μ f t).toNNReal)))) ∧
        -- (3) the empirical measure, weakly in probability
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ h : ℝ →ᵇ ℝ, ∀ η : ℝ, 0 < η →
          Tendsto (fun k => (S k).P {ω | η ≤ |(N k : ℝ)⁻¹ * ∑ i, h ((S k).X t ω i) -
              ∫ x, h x ∂(gaussianReal 0 (Vmu σ c T μ f t).toNNReal)|}) atTop (𝓝 0)) ∧
        -- (4) the time-zero values
        ((∀ k v, GraphLQGame.Equilibrium.cost (G k) c T (S k) v ≠ ⊤) ∧
          Tendsto (fun k => (N k : ℝ)⁻¹ * ∑ v, (GraphLQGame.Equilibrium.cost (G k) c T (S k) v).toReal) atTop
            (𝓝 (-(σ ^ 2 / 2) * Real.log (∫ l in Set.Icc (-2 : ℝ) 0, -l / (1 - l * f T) ∂μ)))) := by sorry

end GraphLQGame.Asymptotics
