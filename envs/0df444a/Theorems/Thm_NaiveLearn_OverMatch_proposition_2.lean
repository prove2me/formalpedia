-- Prove2me | Theorems.Thm_NaiveLearn_OverMatch_proposition_2
-- name    : NaiveLearn.OverMatch.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:18.450416+00:00
-- url     : https://prove2.me/theorems/5713703b-03d3-4896-a900-14174abc06da
-- title:
--   Proposition 2, p. 20 (Benaim 1998, Prop. 3.1; Roth–Sandholm 2013, Thm 3.1), for the σ-DeGroot process — for small ϵ, x^{⌊t/ϵ⌋} tracks the mean-field ODE on [0, T]
-- statement:
--   Let $\sigma$ map $[0,1]$ into $[0,1]$ and be Lipschitz on $[0,1]$, and let $W$ be the weight matrix of a strongly connected network (row-stochastic, irreducible, $w_{ii}>0$). For an initial belief $\mathbf x^1\in[0,1]^m$ let $\mathbf x^t$ be the beliefs of the random $\epsilon$-DeGroot process with decision rule $\sigma$, let $y(t)=\mathbf x^{\lfloor t/\epsilon\rfloor}$ be its interpolation on the time scale $\epsilon$, and let $z$ be the solution of the mean-field equation
--   $$
--   \dot z=W\vec\sigma(z)-z,\qquad z(0)=\mathbf x^1 .
--   $$
--   Then for every $T>0$ and $\eta>0$,
--   $$
--   \lim_{\epsilon\to0}\ \Pr\Big(\sup_{0\le t\le T}\|z(t)-y(t)\|>\eta\Big)=0,
--   $$
--   uniformly in $\mathbf x^1\in[0,1]^m$: for every $\gamma>0$ there is $\epsilon_0>0$ such that the probability is at most $\gamma$ for all $\epsilon\in(0,\epsilon_0)$ and all $\mathbf x^1\in[0,1]^m$.
--
--   For $\sigma=\mathrm{id}$ the mean-field equation is (6)–(7), $\dot z=(W-I)z$; for an extremization rule $\sigma_\delta$ it is (10). This is the stochastic-approximation step that reduces the random process to an ordinary differential equation.
--
--   **Formalization Note** The paper states the proposition for an abstract Markov process satisfying (3) and cites it from Benaim (1998) and Roth–Sandholm (2013); it is posed here for the belief process of this model, which covers both of the paper's uses. The printed conditioning "$y(0)=z(0)=\mathbf x^1$ … uniformly in $x^0\in X$" names one initial point twice and is read as uniformity in $\mathbf x^1$. $\|\cdot\|$ is the sup norm. Lean time $0$ is the paper's period $1$, so $y(t)$ is `beliefAct σ ε W x1 U ⌊t/ε⌋₊`. In the mean field each coordinate is projected onto $[0,1]$ before $\sigma$ is applied, which does not affect solutions started in $[0,1]^m$; the field is then globally Lipschitz, so the solution exists and is unique.
-- source:
--   Arieli, Babichenko & Mueller-Frank, Naive Learning Through Probability Over-Matching, SSRN working paper 3338015 (version of August 3, 2020), p. 20, Proposition 2, (3), (4), (6), (7); p. 22, (10)

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace NaiveLearn.OverMatch

/-- Proposition 2, p. 20 (Benaim 1998, Prop. 3.1; Roth–Sandholm 2013, Thm 3.1), for the
`σ`-DeGroot process: for every `T > 0` and `η > 0`, the probability that the interpolated path
`y(t) = x^{⌊t/ε⌋}` leaves the `η`-tube around the solution `z` of `ż = W σ⃗(z) − z`, `z(0) = x¹`, on
`[0, T]` tends to `0` as `ε → 0`, uniformly in `x¹ ∈ [0, 1]^m`. -/
theorem proposition_2 {m : ℕ} (σ : ℝ → ℝ) (hσmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (K : NNReal) (hσlip : LipschitzOnWith K σ (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : IsWeightMatrix W) :
    ∀ T : ℝ, 0 < T → ∀ η : ℝ, 0 < η → ∀ γ : ℝ, 0 < γ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) ε0, ∀ x1 : Fin m → ℝ,
        (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) →
        ∀ z : ℝ → (Fin m → ℝ), IsODESolution (meanField σ W) z → z 0 = x1 →
          coinLaw m {U | ∃ t ∈ Set.Icc (0 : ℝ) T,
              η < ‖z t - beliefAct σ ε W x1 U ⌊t / ε⌋₊‖} ≤ ENNReal.ofReal γ := by sorry

end NaiveLearn.OverMatch
