-- Prove2me | Theorems.Thm_OfflineStochMatchFull_InfinitePatience_corollary_5_full
-- name    : OfflineStochMatchFull.InfinitePatience.corollary_5_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:48:57.960295+00:00
-- url     : https://prove2.me/theorems/8a398695-0285-425c-b416-2c139139b086
-- title:
--   Corollary 5 — full infinite-patience approximation and causal balanced RCRS
-- statement:
--   Let $G=(V,E)$ be a finite loopless undirected graph, with independent hidden activation probabilities $p_e\in[0,1]$, nonnegative real weights $w_e$, and all patience bounds $t_v=\infty$. Select either $\widetilde a(z)=\exp(-z/2)$ or $\widetilde a(z)=1-z/2$. Set
--
--   $$
--   c=\int_0^1\exp(-2x)\,dx=\frac{1-\exp(-2)}2.
--   $$
--
--   The exact constant satisfies $0<c\le1$. Algorithm 1 uses an independent uniform permutation and independent Bernoulli sampling, attenuation and activeness bits. Its probing decisions depend only on earlier observed probes and current private bits; active probes are immediately committed, every prefix is an active matching and commitments persist.
--
--   For every feasible solution $y$ of LP (3), the execution law is normalized and nonnegative, every order has probability $1/|E|!$, and
--
--   $$
--   \Pr[e\text{ is probed}]\ge cy_e\quad(e\in E),\qquad
--   \operatorname{ALG}(y)\ge c\sum_{e\in E}w_ep_ey_e,
--   $$
--
--   where $\operatorname{ALG}(y)$ is the expected weight of the actual terminal matched-edge set. The LP and adaptive-policy optima are nonempty, bounded and attained. An LP maximizer $y^*$ exists; for every such maximizer and every admissible adaptive randomized probing policy $\pi$,
--
--   $$
--   \operatorname{ALG}(y^*)\ge cR(\pi),\qquad
--   \operatorname{ALG}(y^*)\ge c\mathrm{OPT}.
--   $$
--
--   Finally, for every $\zeta\in[0,1]^E$ satisfying $\sum_{e\in\delta(v)}\zeta_e\le1$ at every vertex, $p=\zeta,y=1,t=\infty$ is LP feasible. The instantiated scheme accepts an arriving edge precisely when it is active, both endpoints are unmatched and its independent attenuation bit is one. It is a causal random-order contention resolution scheme: each arrival is immediately accepted or irrevocably discarded, the output is an active matching, and
--
--   $$
--   \Pr[e\text{ is accepted}]\ge c\zeta_e\quad(e\in E).
--   $$
--
--   The assertion includes a normalized law with independent uniform order and a pathwise coupling to Algorithm 1. It covers the entire degree-relaxation domain used in Definition 1, including zero coordinates and empty graphs. The probability clause holds for every feasible $y$; the approximation comparison uses the optimal LP choice prescribed in §2.
--
--   **Formalization Note** The constant is exact, independent of every instance parameter and of the attenuation choice. All patiences are genuine infinite values. Expected rewards come from execution, and causality is a property of the specified arrival transition.
--
--   Differences from the source:
--   - generalization: the source graph has edges that are unordered pairs of distinct vertices → the reused loopless graph interface also permits parallel edges; reason: every finite simple source graph embeds by an injective endpoint map; the stated bounds also hold for distinct parallel edge labels
--   - reading: the effective attenuation functions from Definition 4 with α=1/2 → the exponential and linear attenuation functions at α=1/2; reason: the sentence immediately before Corollary 5 explicitly specifies these two functions; the third function has no α parameter
--   - reading: for any feasible y the probing guarantee holds, and the algorithm is an approximation → the probing and LP-weight guarantees hold for every feasible y, while approximation to all policies uses an LP maximizer; reason: §2 p. 7 and §3.1 p. 8 prescribe an optimal LP solution for approximation; arbitrary y=0 would otherwise contradict a positive optimum
--   - encoding: adaptive randomized probe-commit algorithms with arbitrary independent internal randomness → normalized PMFs on next-edge-or-stop actions at observable probe histories, with the induced finite execution expectation; reason: conditional action distributions represent every admissible randomized policy; no edge repeats and all runs have at most |E| probes
--   - encoding: optimal objective LP and an optimal probing algorithm → real suprema of feasible LP and actual policy rewards, with nonemptiness, boundedness, and attainment asserted as conclusions; reason: the source finite problem has a feasible zero LP vector and a legal stopping policy; these conclusions exclude default suprema without assuming the comparison theorem
--   - encoding: random-order probing and random-order contention resolution → finite permutation and independent Bernoulli sums, explicit sequential acceptance, prefix causality and coupling; reason: presampling independent hidden bits changes no execution because a probe reads its bit only after its decision, and the CRS reads only current and earlier arrivals
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3 (20 April 2026), https://arxiv.org/abs/2106.06892v3, §3.3, Corollary 5 p. 16, all clauses; §2 LP (3), optimal-LP prescription and Definitions 1–2 pp. 7–8; §3.1 Algorithm 1 p. 8, §3.2 Equation (4) p. 9.

import Mathlib
import Definitions.Def_OfflineStochMatchFull_InfinitePatience_Values
import Definitions.Def_OfflineStochMatchFull_InfinitePatience_RCRS
import Theorems.Thm_OfflineStochMatch_InfinitePatience_effective_exp_lin
import Theorems.Thm_OfflineStochMatch_InfinitePatience_corollary_5

namespace OfflineStochMatchFull.InfinitePatience

open OfflineStochMatch.InfinitePatience

/-- Full Corollary 5, arXiv:2106.06892v3, §3.3, p. 16, with the
optimal-LP prescription of §2 p. 7 and the causal CRS reduction of Definitions
1–2 pp. 7–8. Exact constant, both named attenuation choices, full degree domain.
The graph interface also admits parallel edges, a disclosed generalization. -/
theorem corollary_5_full {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p w : E → ℝ) (aT : ℝ → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hw : ∀ e, 0 ≤ w e)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) :
    let t : V → ℕ∞ := fun _ => ⊤
    let c : ℝ := (1 - Real.exp (-2)) / 2
    (∫ x in (0 : ℝ)..1, Real.exp (-2 * x)) = c ∧
    0 < c ∧ c ≤ 1 ∧
    AlgorithmOperational G t ∧ OptimaAttained G p t w ∧
    (∀ y : E → ℝ, LPFeasible G p t y →
      AlgorithmProbabilityLaw p y aT ∧
      (∀ e, c * y e ≤ probProbed G p t y aT e) ∧
      c * lpObjective p w y ≤ algorithmReward G p t y w aT) ∧
    (∃ yStar : E → ℝ, IsLPMaximizer G p t w yStar) ∧
    (∀ yStar : E → ℝ, IsLPMaximizer G p t w yStar →
      (∀ π : ProbingPolicy G t,
        c * policyReward G p t w π ≤ algorithmReward G p t yStar w aT) ∧
      c * OPT G p t w ≤ algorithmReward G p t yStar w aT) ∧
    (∀ ζ : E → ℝ, DegreeRelaxation G ζ →
      LPFeasible G ζ t (fun _ => 1) ∧ BalancedRCRS G ζ aT c) := by sorry

end OfflineStochMatchFull.InfinitePatience
