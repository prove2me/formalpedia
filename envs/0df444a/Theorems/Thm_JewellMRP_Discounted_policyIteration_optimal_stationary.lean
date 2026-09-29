-- Prove2me | Theorems.Thm_JewellMRP_Discounted_policyIteration_optimal_stationary
-- name    : JewellMRP.Discounted.policyIteration_optimal_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:04:10.673403+00:00
-- url     : https://prove2.me/theorems/f475a952-5fb7-482c-9c7f-0044dfc4dd1b
-- title:
--   p. 947 — the policy-iteration algorithm of Fig. 1 produces an optimal stationary policy as good as any nonstationary policy
-- statement:
--   Let a Markov-renewal program with finitely many states $S$ ($N$ of them) and a nonempty finite set of alternatives ($Z$ of them) be given, and let $\alpha > 0$. Then:
--
--   1. for every stationary policy $d$, the value-determination equations (15) of $d$ have exactly one solution;
--   2. for every run $(d_k, v_k)_{k\ge 0}$ of the algorithm of Fig. 1, there is a cycle $K < Z^N$ with $d_{K+1} = d_K$, and for that $K$:
--      - the $n$-step return of the stationary policy $d_K$ converges to $v_K$ as $n \to \infty$, for every choice of boundary rewards;
--      - for every nonstationary policy $\pi$, every choice of boundary rewards $V^0$ and every state $i$, the $n$-step return $V^\pi_i(n)$ converges to a limit $x$ with $x \le (v_K)_i$;
--      - the optimal $n$-step returns of (6) converge to $v_K$, for every choice of boundary rewards:
--   $$
--   \lim_{n\to\infty} V_i(n,\alpha) = (v_K)_i \qquad\text{for every } i .
--   $$
--
--   The paper states: "Thus the algorithm of Fig. 1 produces an optimal, stationary policy that is as good as any optimal, nonstationary policy", resting on Claims (a)–(d) of p. 946 and the existence of an optimal stationary policy. Together these say that policy iteration solves the infinite-step discounted Markov-renewal program exactly, in finitely many cycles.
--
--   **Formalization Note** "Terminates in a finite number of cycles" is made explicit by the bound $K < Z^N$ (the paper's count of stationary policies). "Optimal" is read as: the returned policy's return $v_K$ dominates the limiting return of every policy of the paper's class (deterministic, Markov, possibly nonstationary) from every state, and equals the "maximum expected, discounted returns" $\lim_n V_i(n,\alpha)$ of (14). All limits are asserted to exist. The one-transition returns $\rho^z_{ij}(\alpha)$ are arbitrary real data, a generalization of the paper's (4). The returns of policies are defined by the one-step recursion of (6).
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, p. 947, The Optimal Policy with Discounting and Fig. 1, with Claims (a)-(d) on p. 946

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- p. 947 with Claims (a)–(d) of p. 946: for `α > 0`, the value-determination equations (15)
of every stationary policy are uniquely solvable, and every run of the algorithm of Fig. 1
reaches two identical successive policies `d K = d (K + 1)` within at most `Z^N` cycles; the
stationary policy `d K` then has limiting return `v K`, which is at least the limiting return
of every nonstationary policy and equals the limit of the optimal `n`-step returns of (6). -/
theorem policyIteration_optimal_stationary {S A : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [Nonempty A] (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    (∀ d : S → A, ∃! v : S → ℝ, SolvesEval M α d v) ∧
    ∀ (d : ℕ → S → A) (v : ℕ → S → ℝ), IsFig1Run M α d v →
      ∃ K, K < Fintype.card (S → A) ∧ d (K + 1) = d K ∧
        (∀ V0 : S → ℝ,
          Tendsto (fun n => policyReturn M α (fun _ => d K) V0 n) atTop (𝓝 (v K))) ∧
        (∀ (π : ℕ → S → A) (V0 : S → ℝ) (i : S), ∃ x : ℝ,
          Tendsto (fun n => policyReturn M α π V0 n i) atTop (𝓝 x) ∧ x ≤ v K i) ∧
        (∀ V0 : S → ℝ, Tendsto (optValue M α V0) atTop (𝓝 (v K))) := by sorry

end JewellMRP.Discounted
