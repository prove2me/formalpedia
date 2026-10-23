-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_lemma_9
-- name    : MNLTrisection.Adaptive.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:36.149029+00:00
-- url     : https://prove2.me/theorems/237b3788-bf8d-449a-b22b-88d32bf3e4b4
-- title:
--   Lemma 9, p. 13 — regret in Case 1: ψ¹_τ(α, β) ≤ βT + Σ_{τ'} [sup_{Δ>ε_τ'} ΔT e^{−n_τ'Δ²} + O(ε_τ'^{-1} log(Tε_τ'²))]
-- statement:
--   Throughout, there are $N$ items with known revenues $r_i \in [0,1]$ and unknown utilities $v_i \ge 0$, the no-purchase utility is $v_0 = 1$, and $R(S) = \sum_{j\in S} r_j v_j/(1+\sum_{j\in S} v_j)$ is the expected revenue (2) of an assortment $S \subseteq [N]$. Run the adaptive-confidence trisection policy for $T$ periods, with $\varepsilon_\tau = \tfrac13(\tfrac23)^\tau$, $n_\tau = 8\lceil \varepsilon_\tau^{-2}\ln(8T\varepsilon_\tau^2)\rceil$, and $\bar\tau(T)$ the last epoch that can start. Let $\psi^1_\tau(\alpha,\beta)$ be the expected regret of epochs $\tau, \dots, \tau_0$ conditioned on $\mathcal E_1(\tau) : \theta^* < a_\tau < b_\tau$, $|a_\tau - \theta^*| = \alpha$, $|F(a_\tau) - a_\tau| = \beta$ (14). There is a universal constant $C > 0$ such that for all $N$, $v$, $r$, every $T \ge 25$, every epoch $\tau$ with $\sum_{\tau'<\tau} n_{\tau'} < T$, and all $\alpha, \beta \ge 0$,
--   $$\psi^1_\tau(\alpha,\beta) \le \beta T + \sum_{\tau'=\tau}^{\bar\tau(T)}\Big[\sup_{\Delta > \varepsilon_{\tau'}} \Delta T e^{-n_{\tau'}\Delta^2} + C\,\varepsilon_{\tau'}^{-1}\log(T\varepsilon_{\tau'}^2)\Big].$$
--
--   This is the recursion for the case where the search interval has moved to the right of the optimal level.
--
--   **Formalization Note** Three repairs of the printed statement, all following its proof (Supplement p. 8): the sum starts at $\tau' = \tau$ (printed $\tau+1$, which omits epoch $\tau$'s own exploration and fails when $\tau$ is the last epoch); the exponent uses $n_{\tau'}$ (printed $n_\tau$); the random upper limit $\tau_0$ is replaced by the deterministic $\bar\tau(T) \ge \tau_0$, every summand being nonnegative. $T \ge 25$ and "epoch $\tau$ can start" are added so that $\log(T\varepsilon^2) > 0$; without them the $O$-term can be negative. $O(\cdot)$ is a universal constant $C$ chosen before every other quantity. Inner-iteration counts are $\max(1, n_\tau)$.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, p. 13, Lemma 9 and (14); proof in Supplement p. 8 (PDF 27)

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

/-- **Lemma 9** (Regret in Case 1, p. 13), with the sum starting at `τ' = τ` as in its proof
(Supplement p. 8) and running to the last epoch `τ̄(T)` that can start:
`ψ¹_τ(α, β) ≤ βT + ∑_{τ'=τ}^{τ̄} [sup_{Δ > ε_τ'} ΔT exp{−n_τ' Δ²} + C ε_τ'^{-1} log(T ε_τ'²)]`
for a universal `C`, whenever `T ≥ 25` and epoch `τ` can start (`∑_{τ' < τ} n_τ' < T`). -/
theorem lemma_9 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (v r : Fin N → ℝ), (∀ i, 0 ≤ v i) →
      (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ T τ : ℕ, 25 ≤ T → ∑ τ' ∈ Finset.range τ, nEpoch T τ' < T →
      ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      psi v r T 1 τ α β ≤ β * T + ∑ τ' ∈ Finset.Icc τ (tauBar T),
        ((⨆ Δ : {Δ : ℝ // eps τ' < Δ},
            (Δ : ℝ) * T * Real.exp (-((nEpoch T τ' : ℝ) * (Δ : ℝ) ^ 2))) +
          C * (eps τ')⁻¹ * Real.log (T * eps τ' ^ 2)) := by sorry

end MNLTrisection.Adaptive
