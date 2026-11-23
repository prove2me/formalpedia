-- Prove2me | Theorems.Thm_GradDOvS_Submod_Supplement_theorem_5
-- name    : GradDOvS.Submod.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:19:58.366366+00:00
-- url     : https://prove2.me/theorems/4e1975f3-93d9-4b57-b2b2-faf7274aea00
-- title:
--   Theorem 5, p. 24 (constant of EC.4.1) — every (ε, δ)-PGS algorithm for L♮-convex simulation models needs T(ε, δ, MC) ≥ dσ²/(72ε²)·log(1/(2.4δ))
-- statement:
--   Let $d \ge 1$, $N \ge 2$, $\sigma > 0$, $\epsilon > 0$ and $\delta \in (0,1)$. Let $\mathcal{MC} = \mathcal{MC}(d,N,\sigma)$ be the class of simulation models on $\mathcal X = [N]^d$ whose outputs $F(x,\xi_x)$ are sub-Gaussian with parameter $\sigma^2$ (Assumption 1) and whose objective $f(x) = \mathbb E[F(x,\xi_x)]$ is L♮-convex (Assumption 2). Then the expected simulation cost of the $(\epsilon,\delta)$-PGS guarantee (Definition 2) satisfies
--   $$T(\epsilon,\delta,\mathcal{MC}) \ \ge\ \frac{d\,\sigma^2}{72\,\epsilon^2}\,\log\!\Big(\frac{1}{2.4\,\delta}\Big).$$
--   Equivalently: for every simulation-optimization algorithm that stops almost surely and returns an $\epsilon$-optimal point with probability at least $1-\delta$ on every model of $\mathcal{MC}$, there are models of $\mathcal{MC}$ on which its expected number of simulations is arbitrarily close to, or above, the right-hand side.
--
--   The bound matches the upper bound of Theorem 2 in its dependence on $\epsilon$ and $\delta$ up to a factor $d$ and logarithmic terms, and shows that no algorithm can avoid a cost linear in the dimension.
--
--   **Formalization Note** The cost is in $[0,\infty]$; for $\delta \ge 1/2.4$ the right-hand side is non-positive and is read as $0$. Algorithms are the platform's bandit protocol on the $N^d$ points: a sampling kernel of the history, a stopping time of the observation filtration and a recommendation measurable at the stopping time.
--
--   Differences from the source:
--   - reading: $T(\epsilon,\delta,\mathcal{MC}) \ge \Theta[(d/\epsilon^2)\log(1/\delta)]$ → $T(\epsilon,\delta,\mathcal{MC}) \ge d\sigma^2/(72\epsilon^2)\cdot\log(1/(2.4\delta))$ for every $\epsilon > 0$ and $\delta \in (0,1)$; reason: the $\Theta$ has no stated constant; the proof, p. ec24 (PDF 62), concludes $\mathbb E_{M_0}[\tau] \ge d\sigma^2/(72\epsilon^2)\log(1/(2.4\delta))$, and for $\delta \ge 1/2.4$ the bound is trivially true
--   - generalization: the sampling rule chooses the next point from the history → it may also use internal randomization (a Markov kernel of the history); reason: the infimum ranges over a larger class of algorithms, so the bound is stronger; deterministic rules are the Dirac kernels
--   - encoding: models, algorithms and $\mathbb E_M[\tau]$ of §2 → stochastic bandits on the $N^d$ points with the platform's trajectory law, stopping times of the natural filtration, recommendations measurable at the stopping time, and the cost in $[0,\infty]$; reason: standard formal rendering of §2.1 (p. 11), including the a.s. finiteness of the stopping time the paper assumes
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 24, Theorem 5; constant from its proof, pp. ec20–ec24 (PDF 58–62), final display on p. ec24 (PDF 62); setting pp. 9–14 (Assumptions 1–3, Definitions 1–3)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Supplement_SimCost

open NNReal ENNReal

namespace GradDOvS.Submod.Supplement

/-- Theorem 5, p. 24, with the constant of its proof (EC.4.1, p. ec24 = PDF 62): under Assumptions
1–3 (`X = [N]^d`, `N ≥ 2`, `d ≥ 1`; L♮-convex objective; outputs sub-Gaussian with parameter `σ²`),
every admissible simulation-optimization algorithm that is (ε, δ)-PGS on every model of `MC` has
worst-case expected simulation cost at least `dσ²/(72ε²) · log(1/(2.4δ))`:
`T(ε, δ, MC) ≥ dσ²/(72ε²) · log(1/(2.4δ))`. -/
theorem theorem_5 (d N : ℕ) (hd : 1 ≤ d) (hN : 2 ≤ N) (σ : ℝ≥0) (hσ : 0 < σ) (ε δ : ℝ)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal ((d : ℝ) * (σ : ℝ) ^ 2 / (72 * ε ^ 2) * Real.log (1 / (2.4 * δ))) ≤
      costPGS d N σ ε δ := by sorry

end GradDOvS.Submod.Supplement
