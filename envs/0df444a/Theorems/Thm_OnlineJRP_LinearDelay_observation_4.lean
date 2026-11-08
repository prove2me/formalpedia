-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_observation_4
-- name    : OnlineJRP.LinearDelay.observation_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:38.465632+00:00
-- url     : https://prove2.me/theorems/e75fb0cc-f341-427a-9be1-c98079302e35
-- title:
--   Observation 4 — $\mathrm{sl}(\tau_{\min})\ge 1$ at every call implies Theorem 1
-- statement:
--   If $\mathrm{sl}(\tau_{\min})\ge 1$ at every call to PlanPurchase, for every number of items, all item costs and instances and every run at joint cost $1$, then Theorem 1 holds: there is a deterministic online algorithm with a feasible output of cost at most $\rho\cdot\mathrm{OPT}$ on every instance.
--
--   The step passes from the analysis of Algorithm 1 to the formal competitive bound: choosing $H$ as a function of the state, termination, causality, the scaling from joint cost $1$ to any joint cost, and the passage from the internal cost to the cost of the model.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
--   - reading: a purchase (t, S) serves every r with i_r ∈ S and t_r ≤ t (p. 1), while Algorithm 1 processes planned purchases before arrivals (p. 4) → the conclusion uses cost of the model; the hypothesis uses the internal states, where a request released exactly at a purchase's time stays live; reason: for the same purchases formal cost ≤ internal cost and any request served internally is served formally
--   - reading: We normalize the joint cost to cjoint = 1 → the hypothesis is at joint cost 1, and the conclusion is for every cjoint > 0; reason: scaling c and the weights by 1/cjoint keeps release times and causality, so the general case is a step of the proof, as on p. 1
--   - reading: online: request r is revealed at time t_r; deterministic → OnlineAlg: a function from request lists to purchase lists, with causal: on two instances with the same requests released by time T, the purchases at times ≤ T coincide, in the same order; reason: this is what revealed at time t_r means for a map on whole inputs; without it the offline optimum would be a witness at ratio 1
--   - reading: An instance is [n] and a request sequence, with the costs cjoint, c_i → the algorithm gets n and the costs as parameters, A n P; only the requests are online; reason: the page treats the costs as given and only the requests as revealed over time
--   - encoding: a finite sequence of requests → a list in release order, simultaneous requests in any fixed order, with IsInstance; reason: every finite family can be listed this way, so no instance is lost; equal triples remain distinct list entries
--   - encoding: a solution is a set of purchases; OPT is the optimal offline cost → a finite list of purchases; OPT is sInf of the costs of feasible lists; reason: a repeated purchase only costs more and an infinite set has infinite cost, so the infimum is the same; the set is nonempty and bounded below on an instance
--   - encoding: x ≈ 1.7549 is the unique real root of (1), ρ := 1 + x → x is a binder with hypothesis x (x − 1)² = 1 and ρ is written 1 + x; reason: existence and uniqueness of the root are proved in the mission's sanity checks, so the binder is not vacuous
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Observation 4, p. 9

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt
import Definitions.Def_OnlineJRP_LinearDelay_OnlineAlg

namespace OnlineJRP.LinearDelay

/-- Observation 4, p. 9 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): if `sl(τmin) ≥ 1` at every call to `PlanPurchase`, then Theorem 1 holds.

**Formalization Note** "Every call" is over every number of items, all item costs `≥ 0` at joint cost `1`, every instance, every run with any admissible `H`, and every state of phase `call`. The conclusion is the full statement of `theorem_1` for this `x`, so the proof supplies the algorithm as a function (fixing `H`), termination, causality, the scaling from `cjoint = 1` and the passage from the internal cost to `cost`. -/
theorem observation_4 (x : ℝ) (hx : x * (x - 1) ^ 2 = 1)
    (h : ∀ (n : ℕ) (c : Fin n → ℝ), (∀ i, 0 ≤ c i) → ∀ σ : List (Req n), IsInstance σ →
      ∀ l : List (St n), IsRun x c σ l → ∀ st ∈ l, st.phase = .call →
        1 ≤ st.sl x c st.τmin) :
    ∃ A : ∀ n : ℕ, Params n → OnlineAlg n,
      ∀ (n : ℕ) (P : Params n) (σ : List (Req n)), IsInstance σ →
        IsFeasible ((A n P).run σ) σ ∧ cost P ((A n P).run σ) σ ≤ (1 + x) * OPT P σ := by sorry

end OnlineJRP.LinearDelay
