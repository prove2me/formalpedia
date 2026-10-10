-- Prove2me | Theorems.Thm_GraphLQGame_DenseApprox_theorem_2_11
-- name    : GraphLQGame.DenseApprox.theorem_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:25:56.446531+00:00
-- url     : https://prove2.me/theorems/1658f572-a9a0-4c6b-9c33-1b1ad2061b68
-- title:
--   Theorem 2.11 — on any finite graph the mean-field control $\alpha^{\mathrm{MF}}$ is an $\epsilon^G$-Nash equilibrium, with $\epsilon^G_v\propto\deg_G(v)^{-1/2}$
-- statement:
--   Let $G$ be a finite graph on $V=\{1,\dots,n\}$, let $T,\sigma,c>0$, and give every player $v$ the control
--   $$\alpha^{\mathrm{MF}}_v(t,x)=\frac{-cx_v}{1+c(T-t)},\qquad t\in[0,T],\ x\in\mathbb R^V.$$
--   Define $\epsilon^G\in\mathbb R^V_+$ by $\epsilon^G_v=\sigma^2\frac{cT}{1+cT}\sqrt{\frac{cT(2+cT)}{\deg_G(v)}}$ if $\deg_G(v)\ge1$ and $\epsilon^G_v=0$ if $\deg_G(v)=0$. Then $(\alpha^{\mathrm{MF}}_v)_{v\in V}$ is a Markovian $\epsilon^G$-Nash equilibrium on $G$. In particular, with $\delta(G)=\min_v\deg_G(v)$ and
--   $$\epsilon_G=\sigma^2\frac{cT}{1+cT}\sqrt{\frac{cT(2+cT)}{1\vee\delta(G)}},$$
--   it is a Markovian $\epsilon_G$-Nash equilibrium on $G$. The state equation for this profile with zero initial states has a solution.
--
--   The theorem gives a quantitative threshold on how dense a graph must be for the mean field approximation to hold: along a graph sequence with $\delta(G_n)\to\infty$, the decentralized controls $\alpha^{\mathrm{MF}}$ form $\epsilon_{G_n}$-Nash equilibria with $\epsilon_{G_n}\to0$, with no transitivity assumed.
--
--   **Formalization Note** Initial states are $0$. The statement on p. 10 does not mention $X(0)$; §2.1 fixes non-random initial states that "in many cases" are zero, and the proof ((7.6), Lemma 7.2, (7.7)) is for $X(0)=0$. With non-zero initial states the claim fails in general, so this is a disclosed hypothesis. The existence of a solution is asserted, which the paper presupposes; without it the Nash property would hold vacuously. The printed "for each $n$" refers to no $n$ and is ignored. $T,\sigma,c>0$ are the standing assumptions of §2.1. Vertices are `Fin n`: the paper's $\{1,\dots,n\}$ become $\{0,\dots,n-1\}$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Theorem 2.11, §2.3.1, p. 10

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_DenseApprox_MeanField

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GraphLQGame.DenseApprox

open EthierKurtz

/-- **Theorem 2.11** (Approximate equilibria on general dense graphs; Lacker–Soret,
arXiv:2005.14102v2, §2.3.1, p. 10). Let `G` be a finite graph and `α^MF_v(t, x) = −c x_v/(1 + c(T − t))`.
Then `(α^MF_v)_v` is an `ε^G`-Nash equilibrium on `G`, where
`ε^G_v = σ² (cT/(1+cT)) √(cT(2+cT)/deg_G(v))` if `deg_G(v) ≥ 1` and `ε^G_v = 0` if `deg_G(v) = 0`;
in particular it is an `ε_G`-Nash equilibrium with
`ε_G = σ² (cT/(1+cT)) √(cT(2+cT)/(1 ∨ δ(G)))`, `δ(G) = min_v deg_G(v)`.

Formalization Note:
* `G` is any finite simple graph on `Fin n` (the paper's `{1, …, n}` become `{0, …, n − 1}`);
  isolated vertices are allowed.
* **Initial states are zero** (`x0 = 0`), a disclosed hypothesis: the statement does not mention
  `X(0)`, but §2.1 fixes non-random initial states, "in many cases" zero, and the whole proof
  ((7.6), Lemma 7.2, (7.7)) is for `X(0) = 0`; with non-zero initial states the claim fails in
  general.
* The conclusion also asserts that the state equation (2.1) for `α^MF` has a solution, which the
  paper presupposes; otherwise the Nash property would hold vacuously.
* `IsMarkovNash` compares costs over any solutions for the profile and for each deviation, which is
  faithful by strong uniqueness for (2.1); costs are `ℝ≥0∞`-valued.
* The printed "for each n" in the statement refers to no `n` and is ignored.
* `T > 0`, `σ > 0`, `c > 0` are the standing assumptions of §2.1. -/
theorem theorem_2_11 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) :
    Nonempty (GraphLQGame.Equilibrium.StateSol n T σ 0 (mfProfile c T)) ∧
    GraphLQGame.Equilibrium.IsMarkovNash G c T σ 0 (epsG σ c T G) (mfProfile c T) ∧
    GraphLQGame.Equilibrium.IsMarkovNash G c T σ 0 (fun _ => epsScalar σ c T G) (mfProfile c T) := by sorry

end GraphLQGame.DenseApprox
