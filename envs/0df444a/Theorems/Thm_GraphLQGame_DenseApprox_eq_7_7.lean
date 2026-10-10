-- Prove2me | Theorems.Thm_GraphLQGame_DenseApprox_eq_7_7
-- name    : GraphLQGame.DenseApprox.eq_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:25:58.958396+00:00
-- url     : https://prove2.me/theorems/7146831d-681f-406a-abfa-ae59a1917c91
-- title:
--   (7.7) — under $\alpha^{\mathrm{MF}}$ the terminal states are i.i.d. $N(0,\sigma^2T/(1+cT))$, and the neighbour average has second moment $\sigma^2T/(\deg_G(v)(1+cT))$
-- statement:
--   Let $G$ be a finite graph, $T,\sigma,c>0$, and let $\boldsymbol X$ solve the state equation for the mean-field profile $(\alpha^{\mathrm{MF}}_u)_{u\in V}$ with $\boldsymbol X(0)=0$. Then $(X_u(T))_{u\in V}$ are independent Gaussians with mean zero and variance $\sigma^2T/(1+cT)$. Consequently, for every vertex $v$ with $\deg_G(v)\ge1$,
--   $$\mathbb E\Big[\Big(\frac1{\deg_G(v)}\sum_{u\sim v}X_u(T)\Big)^2\Big]=\frac{\sigma^2T}{\deg_G(v)(1+cT)}.$$
--
--   The neighbour average is what player $v$ tracks; (7.7) measures how far it fluctuates, and is the source of the $\deg_G(v)^{-1/2}$ rate of Theorem 2.11.
--
--   **Formalization Note** The law of $X_u(T)$ is stated as the image measure being Mathlib's `gaussianReal 0` with that variance, and independence as mutual independence of the family of coordinates. Initial states are $0$, as throughout §7.2 ((7.6) and Lemma 7.2). Vertices are `Fin n`: the paper's $\{1,\dots,n\}$ become $\{0,\dots,n-1\}$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §7.2, Step 1, p. 42, (7.7) and the sentence before it

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_DenseApprox_MeanField

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GraphLQGame.DenseApprox

open EthierKurtz

/-- **(7.7)** with the sentence before it (Lacker–Soret, arXiv:2005.14102v2, §7.2, Step 1,
p. 42): under the mean-field profile with zero initial states, `(X_u(T))_{u ∈ V}` are i.i.d.
Gaussians with mean zero and variance `σ²T/(1 + cT)`, and therefore, for every vertex `v` with
`deg_G(v) ≥ 1`,
`E[((1/deg_G(v)) Σ_{u∼v} X_u(T))²] = σ²T / (deg_G(v)(1 + cT))`.

Formalization Note: the law statement is `Measure.map` of the coordinate `X_u(T)` equal to
`gaussianReal 0 (σ²T/(1+cT))`; independence is `iIndepFun` of the family of coordinates; the
expectation in (7.7) is a Bochner integral of a square-integrable (Gaussian) quantity. Vertices are
`Fin n`. Initial states are `0` (the page's (7.6)). -/
theorem eq_7_7 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) (S : GraphLQGame.Equilibrium.StateSol n T σ 0 (mfProfile c T)) :
    (∀ u : Fin n, S.P.map (fun ω => S.X T ω u) =
      gaussianReal 0 (σ ^ 2 * T / (1 + c * T)).toNNReal) ∧
    iIndepFun (fun (u : Fin n) (ω : S.Ω) => S.X T ω u) S.P ∧
    ∀ v : Fin n, 1 ≤ G.degree v →
      ∫ ω, (((G.degree v : ℝ))⁻¹ * ∑ u ∈ G.neighborFinset v, S.X T ω u) ^ 2 ∂S.P =
        σ ^ 2 * T / ((G.degree v : ℝ) * (1 + c * T)) := by sorry

end GraphLQGame.DenseApprox
