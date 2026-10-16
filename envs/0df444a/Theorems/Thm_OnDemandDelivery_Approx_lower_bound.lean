-- Prove2me | Theorems.Thm_OnDemandDelivery_Approx_lower_bound
-- name    : OnDemandDelivery.Approx.lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:43.990082+00:00
-- url     : https://prove2.me/theorems/cf82fe94-c33f-40b5-af22-8aa93f933d75
-- title:
--   Appendix D, Proof of Theorem 1, part (1), pp. 34–35 — with ω ≡ 0 off the diagonal, APT^n has value Σ E[ℋ^s(K̄ − ζ^n_{n′})] ≤ E[ℋ_n]
-- statement:
--   Consider the dispatching and routing model under its standing assumptions, a period $1 \le n \le N$ and a driver status $\zeta^n$ with $\zeta^n_{n'} \le \bar K$ for $n \le n' \le N$. Choose the APT parameters $\omega^{n'}_m(K^m) = 0$ for $m < n'$ (the diagonal $\omega^{n'}_{n'}(K) = K$ is part of the model). Then the optimal value of $\mathbf{APT}^n(\zeta^n)$ is attained at $K^{n'} = \bar K - \zeta^n_{n'}$, and it lower-bounds the expected cost-to-go:
--   $$V^n_{APT}(\zeta^n) = \sum_{n'=n}^N \mathbb E_{\mathbb Q^{n'}}\big[\mathcal H^s(\bar K - \zeta^n_{n'}, \mathcal I^{n'}, q^{n'})\big] \le \mathbb E_{\mathbb Q^n}\big[\mathcal H_n(\mathcal I^n, q^n, \zeta^n)\big].$$
--
--   With these parameters every driver is back at the depot at the start of the next period, which yields a lower bounding system. This is the lower-bound half of Theorem 1.
--
--   **Formalization Note.** The hypothesis $\zeta^n_{n'} \le \bar K$ states that the en route drivers are among the $\bar K$ drivers; without it APT is infeasible while the expected cost-to-go may be finite. The value of APT is in $[0,\infty]$ and is $+\infty$ when no $K$ is feasible.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, pp. 34–35, Appendix D, Proof of Theorem 1, part (1)

import Mathlib
import Definitions.Def_OnDemandDelivery_Approx_Setting

open scoped ENNReal NNReal

namespace OnDemandDelivery.Approx
open Model
theorem lower_bound {L : Type*} [Fintype L] (M : Model L) (hM : M.Standing) (n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ M.N) (ζ : ℕ → ℕ) (hζ : ∀ n', n ≤ n' → n' ≤ M.N → ζ n' ≤ M.Kbar) :
    M.Vapt n ζ (fun _ _ _ => 0) = ∑ n' ∈ Finset.Icc n M.N, M.EHs n' (M.Kbar - ζ n') ∧
    ∑ n' ∈ Finset.Icc n M.N, M.EHs n' (M.Kbar - ζ n') ≤ M.EH n ζ := by sorry
end OnDemandDelivery.Approx
