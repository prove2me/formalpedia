-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_Supplement_theorem_7
-- name    : OnlineMatchFrameworks.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:28:52.791235+00:00
-- url     : https://prove2.me/theorems/6c447d97-c6cf-4ada-91c8-e55bdb083997
-- title:
--   Theorem 7 (corrected: the SMALL rule and large set of the proof): a 0.027-approximation for item arrivals
-- statement:
--   A single customer waits $\theta\ge1$ time steps while the items $i\in[m]$ arrive by independent Bernoulli processes with probabilities $q_i$. At each step at most one arrived, never offered item may be offered, and it is bought with probability $p_i$ for a reward $w_i\ge0$. $\mathrm{OPT}$ is the expected reward of the best adaptive policy.
--
--   The algorithm solves LP (6). For $\theta=1$ it offers the best arrived item. For $\theta\ge2$, with large items those having $q_i\ge c/\theta$, it uses the LARGE strategy if the large items carry at least a $(1-\phi)$ share of the LP value, and the SMALL strategy otherwise, in which an arriving small item first decides with probability $x_i/(1-(1-q_i)^\theta)$ whether it wants to be offered. There are parameters $\phi\in(0,1)$, $\rho\in(0,1/2)$ and $c\in(0,1)$ such that on every instance and for every optimal solution of LP (6)
--
--   $$
--   \mathrm{ALG}\ \ge\ 0.027\,\mathrm{OPT}.
--   $$
--
--   This gives a constant-factor black box for matching with two-sided arrivals.
--
--   The algorithm as literally printed on pp.27–28 does not have this property. With the unthinned SMALL rule, a valuable small item among $M$ small items of weight $0$ is offered with probability tending to $0$ as $M\to\infty$. With the large set read as $\{i:x_i\ge c/\theta\}$, many items with $q_i=1$, $p_i=1/\theta$ and $w_i=1$ are all small and are discarded after the first step, so the reward is $1/\theta$ while the optimum exceeds $1-1/e$.
--
--   Differences from the source:
--   - correction: SMALL: choose one of the small arrivals at random and offer it (p.28) → each arriving small item first wants to be offered with probability x_i/(1 − (1 − q_i)^θ), and one of those is chosen uniformly; reason: false as printed: θ = 2, one item with w = p = 1 and M items with w = p = 0, all with q = min(c/4, 1/2), give OPT = 2q − q² and ALG → 0 as M → ∞; the proof of Lemma 4 (pp.49–50) analyses the thinned rule
--   - correction: I_LARGE = {i : x_i ≥ c/θ} (display, p.27) → large items are those with q_i ≥ c/θ; reason: false as printed: M > θ²/c items with q = 1, p = 1/θ, w = 1 and x = θ/M give ALG ≤ 1/θ and OPT ≥ 1 − 1/e for M ≥ θ; the sentence before the display and the proofs (pp.48, 50) have q_i ≥ c/θ
--   - reading: an appropriate choice of parameters ϕ, ρ, c → one choice before all instances, with ϕ ∈ (0,1), ρ ∈ (0,1/2) (p.28) and c ∈ (0,1) (p.52); reason: the constants of the algorithm are fixed; the proof takes ρ = 1/4, ϕ = 0.37, c ≈ 0.9249 (p.53)
--   - reading: a 0.027-approximation → against the optimal adaptive policy, for every optimal solution x of LP (6); reason: the stated goal of §5.3 is the best expected weight; the algorithm does not say which optimal solution is found
--   - encoding: the best expected reward over policies → the finite-horizon dynamic program on (steps left, items not arrived, items available); reason: that state is sufficient for optimal control
--   - reading: weights of edges (p.11), no sign stated → w ≥ 0; reason: weights are prices and rewards; this is the standing convention of the paper and of the published mission
--   - encoding: time steps t ∈ {1, …, θ} → a natural number θ ≥ 1; reason: θ = 0 has no time step and both sides are 0
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Theorem 7, p.29; algorithm §5.3, pp.27–28, as analysed on pp.47–53

import Definitions.Def_OnlineMatchFrameworks_Supplement_ItemArrivalAlgorithm

namespace OnlineMatchFrameworks.Supplement

/-- **Theorem 7 (corrected algorithm description).** arXiv:1907.03963v6, Theorem 7, p.29: "For an
appropriate choice of parameters ϕ, ρ, c, our algorithm is a 0.027-approximation."

**Formalization Note.** The parameters are chosen once, before the instance (the proof takes `ρ = 1/4`,
`ϕ = 0.37`, `c ≈ 0.9249`, p.53), in the ranges `ϕ ∈ (0,1)`, `ρ ∈ (0,1/2)` (p.28) and `c ∈ (0,1)` (p.52).
`OPT` is the optimal adaptive policy, not LP (6). `π_Small` is the thinned rule analysed in the proof of
Lemma 4 (pp.49–50); with the unthinned sentence of p.28 the claim is false. Large means `q_i ≥ c/θ`. -/
theorem theorem_7 :
    ∃ ϕ ρ c : ℝ, 0 < ϕ ∧ ϕ < 1 ∧ 0 < ρ ∧ ρ < 1 / 2 ∧ 0 < c ∧ c < 1 ∧
      ∀ (m : ℕ) (G : ItemArrivalInstance (Fin m)) (x : Fin m → ℝ),
        G.IsLPOptimal x → 0.027 * G.OPT ≤ G.ALG ϕ ρ c x := by sorry

end OnlineMatchFrameworks.Supplement
