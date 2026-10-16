-- Prove2me | Theorems.Thm_OnDemandDelivery_Approx_theorem_1
-- name    : OnDemandDelivery.Approx.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:50.890983+00:00
-- url     : https://prove2.me/theorems/0bfe7a10-e41b-452f-ac5a-ca2ae749fd54
-- title:
--   Theorem 1, p. 13 — APT^n bounds the expected cost-to-go from below and above and is exact in the last period
-- statement:
--   Consider the joint dispatching and routing model **JDR** of a store with $N$ periods and $\bar K$ drivers under its standing assumptions, a period $1 \le n \le N$, and a driver status $\zeta^n$ with $\zeta^n_{n'} \le \bar K$ for $n \le n' \le N$. Let $V^n_{APT}(\zeta^n; \omega)$ be the optimal value of the approximation $\mathbf{APT}^n(\zeta^n)$ with nonnegative parameters $\omega = \{\omega^{n'}_m(K^m)\}$, and $\mathbb E_{\mathbb Q^n}[\mathcal H_n(\mathcal I^n, q^n, \zeta^n)]$ the expected optimal cost-to-go. Then:
--   1. **(lower bound)** for an appropriate choice of $\omega$,
--   $$V^n_{APT}(\zeta^n; \omega) \le \mathbb E_{\mathbb Q^n}\big[\mathcal H_n(\mathcal I^n, q^n, \zeta^n)\big];$$
--   2. **(upper bound)** for every static myopic policy $\pi^{sm}$ feasible for $\mathbf{JDR}^n(\zeta^n)$, with expected cost $J_n(\pi^{sm})$, there is an appropriate choice of $\omega$ with
--   $$\mathbb E_{\mathbb Q^n}\big[\mathcal H_n(\mathcal I^n, q^n, \zeta^n)\big] \le V^n_{APT}(\zeta^n; \omega) \le J_n(\pi^{sm});$$
--   3. **(exactness in the last period)** for every choice of $\omega$,
--   $$V^N_{APT}(\zeta^n; \omega) = \mathbb E_{\mathbb Q^N}\big[\mathcal H_N(\mathcal I^N, q^N, \zeta^n)\big].$$
--
--   The theorem justifies using APT as the lookahead in the rollout policy AJRP: its value can be placed on either side of the true expected cost-to-go by the choice of the en route parameters, and in the last period it is the true value.
--
--   **Formalization Note.** The statement is posed in a pinned-down form. (a) $\mathcal H^s(K, \cdot)$ is the single-period optimum with *at most* $K$ routes, as the paper's proofs use it. (b) The page's "under the assumption that there exists a feasible static myopic policy … can serve as … upper bounding problems with appropriate choices of $\omega$" would be vacuous as printed, because the parameters are unconstrained and $\omega \equiv \bar K + 1$ makes APT infeasible with value $+\infty$. The upper bound is therefore stated for every feasible static myopic policy and capped by that policy's expected cost, as the proof on p. 35 claims; the existence assumption becomes the antecedent of this part, and the lower bound and exactness do not use it. (c) The hypothesis $\zeta^n_{n'} \le \bar K$ (the en route drivers are among the fleet) is added; without it APT is infeasible. The parameters are nonnegative by their type, so the lower bound is not obtained by negative $\omega$ cancelling the fleet limit.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, p. 13, Theorem 1

import Mathlib
import Definitions.Def_OnDemandDelivery_Approx_Setting

open scoped ENNReal NNReal

namespace OnDemandDelivery.Approx
open Model
theorem theorem_1 {L : Type*} [Fintype L] (M : Model L) (hM : M.Standing) (n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ M.N) (ζ : ℕ → ℕ) (hζ : ∀ n', n ≤ n' → n' ≤ M.N → ζ n' ≤ M.Kbar) :
    (∃ ω : ℕ → ℕ → ℕ → ℝ≥0, M.Vapt n ζ ω ≤ M.EH n ζ) ∧
    (∀ π : M.StaticMyopic, π.Feasible n ζ →
      ∃ ω : ℕ → ℕ → ℕ → ℝ≥0, M.EH n ζ ≤ M.Vapt n ζ ω ∧ M.Vapt n ζ ω ≤ π.cost n ζ) ∧
    (∀ ω : ℕ → ℕ → ℕ → ℝ≥0, M.Vapt M.N ζ ω = M.EH M.N ζ) := by sorry
end OnDemandDelivery.Approx
