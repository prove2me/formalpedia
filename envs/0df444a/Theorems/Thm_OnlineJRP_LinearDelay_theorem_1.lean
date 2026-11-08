-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_theorem_1
-- name    : OnlineJRP.LinearDelay.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:24.589575+00:00
-- url     : https://prove2.me/theorems/25c60254-c7ca-46e3-961c-0aa4f4a261f0
-- title:
--   Theorem 1 — a deterministic $\rho$-competitive algorithm for online joint replenishment with linear delays, $\rho=1+x\approx 2.7549$, $x(x-1)^2=1$
-- statement:
--   Let $x\approx 1.7549$ be the real root of $x(x-1)^2=1$ and $\rho=1+x\approx 2.7549$. There is a deterministic online algorithm for the joint replenishment problem with linear delay costs such that, for every number $n$ of items, joint cost $c_{\mathrm{joint}}>0$, item costs $c_i\ge 0$ and finite request sequence with release times $t_r\ge 0$ and weights $w_r>0$, its output is feasible and
--   $$
--   \mathrm{ALG}\le\rho\cdot\mathrm{OPT},
--   $$
--   with no additive constant.
--
--   The previous upper bound for this problem was $3$, and the ratio $\rho$ matches a lower bound the paper cites.
--
--   **Formalization Note** The algorithm receives the number of items and the costs as parameters; only the requests are online, which is expressed by the causality field of `OnlineAlg`.
--
--   Differences from the source:
--   - reading: online: request r is revealed at time t_r; deterministic → OnlineAlg: a function from request lists to purchase lists, with causal: on two instances with the same requests released by time T, the purchases at times ≤ T coincide, in the same order; reason: this is what revealed at time t_r means for a map on whole inputs; without it the offline optimum would be a witness at ratio 1
--   - reading: An instance is [n] and a request sequence, with the costs cjoint, c_i → the algorithm gets n and the costs as parameters, A n P; only the requests are online; reason: the page treats the costs as given and only the requests as revealed over time
--   - encoding: a finite sequence of requests → a list in release order, simultaneous requests in any fixed order, with IsInstance; reason: every finite family can be listed this way, so no instance is lost; equal triples remain distinct list entries
--   - encoding: a solution is a set of purchases; OPT is the optimal offline cost → a finite list of purchases; OPT is sInf of the costs of feasible lists; reason: a repeated purchase only costs more and an infinite set has infinite cost, so the infimum is the same; the set is nonempty and bounded below on an instance
--   - encoding: x ≈ 1.7549 is the unique real root of (1), ρ := 1 + x → x is a binder with hypothesis x (x − 1)² = 1 and ρ is written 1 + x; reason: existence and uniqueness of the root are proved in the mission's sanity checks, so the binder is not vacuous
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Theorem 1, p. 2; x and ρ, Eq. (1), p. 2

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt
import Definitions.Def_OnlineJRP_LinearDelay_OnlineAlg

namespace OnlineJRP.LinearDelay

/-- Theorem 1, p. 2 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): for the root `x` of Eq. (1) and `ρ = 1 + x`, a single deterministic online algorithm has, on every instance, a feasible output of cost at most `ρ · OPT`.

**Formalization Note** The bound is for every `n`, every joint cost `cjoint > 0`, all item costs `≥ 0`, with no additive constant. `OnlineAlg` carries causality (see its docstring). `x` is a binder with Eq. (1) as hypothesis; a real root exists and is unique, by the sanity checks of the mission. -/
theorem theorem_1 (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) :
    ∃ A : ∀ n : ℕ, Params n → OnlineAlg n,
      ∀ (n : ℕ) (P : Params n) (σ : List (Req n)), IsInstance σ →
        IsFeasible ((A n P).run σ) σ ∧ cost P ((A n P).run σ) σ ≤ (1 + x) * OPT P σ := by sorry

end OnlineJRP.LinearDelay
