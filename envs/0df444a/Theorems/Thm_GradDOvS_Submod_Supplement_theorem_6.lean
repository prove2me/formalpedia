-- Prove2me | Theorems.Thm_GradDOvS_Submod_Supplement_theorem_6
-- name    : GradDOvS.Submod.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:20:46.140973+00:00
-- url     : https://prove2.me/theorems/befbc710-42f7-4a1d-8d06-38657ed81590
-- title:
--   Theorem 6, p. 24 (constant of EC.4.2) — every (c, δ)-PCS-IZ algorithm for L♮-convex models with indifference zone c needs T(δ, MC_c) ≥ dσ²/(72c²)·log(1/(2.4δ))
-- statement:
--   Let $d \ge 1$, $N \ge 2$, $\sigma > 0$, $c > 0$ and $\delta \in (0,1)$. Let $\mathcal{MC}_c$ be the class of simulation models on $\mathcal X = [N]^d$ with $\sigma^2$-sub-Gaussian outputs (Assumption 1) whose objective $f$ is L♮-convex (Assumption 2) and has a unique minimizer $x^*$ with $f(x) - f(x^*) \ge c$ for all $x \ne x^*$ (indifference-zone parameter $c$). Then the expected simulation cost of the $(c,\delta)$-PCS-IZ guarantee (Definition 2) satisfies
--   $$T(\delta,\mathcal{MC}_c) \ \ge\ \frac{d\,\sigma^2}{72\,c^2}\,\log\!\Big(\frac{1}{2.4\,\delta}\Big).$$
--   That is, every simulation-optimization algorithm that stops almost surely and returns the optimal point with probability at least $1-\delta$ on every model of $\mathcal{MC}_c$ has worst-case expected cost at least the right-hand side.
--
--   This is the indifference-zone counterpart of Theorem 5; together with the upper bound for the choice $\epsilon = c/2$ in Algorithm 2 it shows the dimension dependence of the PCS-IZ cost.
--
--   **Formalization Note** The cost is in $[0,\infty]$; for $\delta \ge 1/2.4$ the right-hand side is non-positive and is read as $0$. The framework is that of Theorem 5.
--
--   Differences from the source:
--   - reading: $T(\delta,\mathcal{MC}_c) \ge \Theta[(d/c^2)\log(1/\delta)]$ → $T(\delta,\mathcal{MC}_c) \ge d\sigma^2/(72c^2)\cdot\log(1/(2.4\delta))$ for every $c > 0$ and $\delta \in (0,1)$; reason: the $\Theta$ has no stated constant; the proof, p. ec24 (PDF 62), concludes $\mathbb E_{M_0}[\tau] \ge d\sigma^2/(72c^2)\log(1/(2.4\delta))$, and for $\delta \ge 1/2.4$ the bound is trivially true
--   - generalization: the sampling rule chooses the next point from the history → it may also use internal randomization (a Markov kernel of the history); reason: the infimum ranges over a larger class of algorithms, so the bound is stronger; deterministic rules are the Dirac kernels
--   - encoding: models, algorithms, the PCS-IZ guarantee and $\mathbb E_M[\tau]$ of §2 → stochastic bandits on the $N^d$ points with the platform's trajectory law, stopping times, recommendations measurable at the stopping time, $\mathbb P(\tau < \infty \text{ and } \hat x = x^*) \ge 1 - \delta$ for the unique minimizer $x^*$, and the cost in $[0,\infty]$; reason: standard formal rendering of §2.1 (p. 11) and p. 10, including the a.s. finiteness of the stopping time the paper assumes
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 24, Theorem 6; constant from its proof, p. ec24 (PDF 62), EC.4.2; setting pp. 9–14 (Assumptions 1–3, Definitions 1–3, MC_c)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Supplement_SimCost

open NNReal ENNReal

namespace GradDOvS.Submod.Supplement

/-- Theorem 6, p. 24, with the constant of its proof (EC.4.2, p. ec24 = PDF 62): under Assumptions
1–3, every admissible simulation-optimization algorithm that is (c, δ)-PCS-IZ on every model of
`MC_c` has worst-case expected simulation cost at least `dσ²/(72c²) · log(1/(2.4δ))`:
`T(δ, MC_c) ≥ dσ²/(72c²) · log(1/(2.4δ))`. -/
theorem theorem_6 (d N : ℕ) (hd : 1 ≤ d) (hN : 2 ≤ N) (σ : ℝ≥0) (hσ : 0 < σ) (c δ : ℝ)
    (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal ((d : ℝ) * (σ : ℝ) ^ 2 / (72 * c ^ 2) * Real.log (1 / (2.4 * δ))) ≤
      costPCSIZ d N σ c δ := by sorry

end GradDOvS.Submod.Supplement
