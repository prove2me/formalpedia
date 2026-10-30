-- Prove2me | Theorems.Thm_MirrorBP_JEA_theorem_1
-- name    : MirrorBP.JEA.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:54.043712+00:00
-- url     : https://prove2.me/theorems/e9dc2239-00a3-4b41-9668-d5ea77eaf702
-- title:
--   Theorem 1, pp. 13–14 — Mirror Backpressure loses at most Cm(K/T + √(ηK)) + Cm²/K per customer for K ≥ poly(m, 1/α_min)
-- statement:
--   There are a universal constant $C < \infty$ and a polynomial bound $K_1 = c\,(m + 1/\alpha_{\min})^N$ (with $C, c, N$ independent of the instance) such that the following holds. Let $V$ be a finite set of $m > 1$ nodes, $\mathcal T$ a finite set of demand types with nonempty pick-up and drop-off neighborhoods $\mathcal P(\tau), \mathcal D(\tau) \subseteq V$, and payoffs $|w_{j\tau k}| \le 1$. Let $T \ge 1$ and let $\boldsymbol\phi^0, \dots, \boldsymbol\phi^{T-1}$ be demand arrival rates that satisfy Condition 1 ($\alpha(\boldsymbol\phi^t) > 0$ for every period) and vary $\eta$-slowly (Definition 1), and let $\alpha_{\min} = \min_{t<T}\alpha(\boldsymbol\phi^t)$. For every number of supply units $K \ge K_1$, the Mirror Backpressure policy (Algorithm 1) with the congestion function (8) and any argmax tie-break satisfies
--   $$L^{\mathrm{MBP}}_T \le M_1\Big(\frac KT + \sqrt{\eta K}\Big) + M_2\frac1K, \qquad M_1 = Cm,\ M_2 = Cm^2,$$
--   where $L^{\mathrm{MBP}}_T = W^*_T - W^{\mathrm{MBP}}_T$ compares the best feasible policy from its best initial state with MBP from its worst initial state (4), (6). Explicitly: for every feasible policy $\pi$ (which may know the rates) and all $\mathbf q, \mathbf q' \in \Omega_K$,
--   $$\frac1T\Big(\sum_{t<T}\mathbb E[v^\pi[t]\mid\mathbf q[0]=\mathbf q] - \sum_{t<T}\mathbb E[v^{\mathrm{MBP}}[t]\mid\mathbf q[0]=\mathbf q']\Big) \le Cm\Big(\frac KT + \sqrt{\eta K}\Big) + \frac{Cm^2}{K}.$$
--
--   This is the paper's main result: a policy that never sees the arrival rates loses $O(K/T + 1/K + \sqrt{\eta K})$ per customer against the optimal rate-aware policy, under the no-underflow constraint.
--
--   **Formalization Note** No sign condition on $\eta$ is stated: for $T \ge 2$ Definition 1 forces $\eta \ge 0$, and for $T = 1$ the bound holds through the term $CmK/T$.
--
--   Differences from the source:
--   - generalization: max_{τ, j ∈ P(τ), k ∈ D(τ)} |w_{jτk}| = 1 → |w j τ k| ≤ 1 for j ∈ P τ, k ∈ D τ; reason: the scaling is 'without loss of generality' (p. 10); every instance with max |w| = 1 satisfies |w| ≤ 1.
--   - reading: type set 𝒯 (finiteness implicit) → [Fintype Ty]; reason: the model is 'a finite-state Markov chain' and SPP 'a linear program' with sums over 𝒯 (pp. 9, 15); Appendix C's remark on infinitely many types presupposes finitely many in the model.
--   - generalization: a policy maps the history of types and states (τ[t′], q[t′])_{t′≤t} to a randomized decision → Policy: (period, past (state, type, decision) triples, current state, current type) ↦ probability vector on feasible decisions; reason: the class contains every policy of 𝒰, so the benchmark W*_T can only grow; MBP belongs to both classes.
--   - encoding: periods t = 1, …, T in (4) and Definition 1 (0, …, T−1 elsewhere) → periods t = 0, …, T − 1 with rates phi t and start state q[0]; reason: the paper mixes both conventions; same instances after an index shift.
--   - encoding: E[v^π[t] | q[0] = q] over the random arrivals and decisions → expPayoff, the finite recursion over types and decisions; reason: each period has finitely many outcomes; the recursion is the law of the controlled chain.
--   - encoding: (1/(T−1)) Σ_{t=1}^{T−1} ‖φ^{t+1} − φ^t‖₁ ≤ η → Σ_{t<T−1} Σ_τ |phi (t+1) τ − phi t τ| ≤ (T − 1) η; reason: multiplied out by T − 1; identical for T ≥ 2, and the paper's expression is undefined for T = 1.
--   - generalization: (j*, k*) = argmax_{j ∈ P(τ), k ∈ D(τ)} of the score → any tie-break sel with IsArgmaxSel; reason: the paper's argmax is some tie-break; the statement holds for every one.
--   - encoding: K₁ = poly(m, 1/α_min), C universal → ∃ C c N before every type and instance binder, K ≥ c (m + 1/α_min)^N; reason: a polynomial in (m, 1/α) with m ≥ 2 is bounded by c (m + 1/α)^N, and conversely; C, c, N do not depend on the instance.
--   - reading: α_min = min_{1≤t≤T} α(φᵗ) → Condition 1 and α_min over the periods t < T; reason: the periods of the horizon under the 0-based convention.
--   - encoding: L_T^MBP = W*_T − W_T^MBP = sup_π max_q (1/T)Σ E[v^π] − min_{q′} (1/T)Σ E[v^MBP] → ∀ π, ∀ q q′ ∈ Ω_K, (expPayoff π q − expPayoff MBP q′)/T ≤ bound; reason: equivalent to L_T ≤ bound without a real sSup.
--   - encoding: horizon T (with 1/T) → 0 < T; reason: excludes T = 0, where 1/T is undefined.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, pp. 13–14, Theorem 1 (footnote 4)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem theorem_1 :
    ∃ C : ℝ, ∃ c : ℝ, ∃ N : ℕ,
      ∀ (V Ty : Type) [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
        (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (T : ℕ) (eta : ℝ) (K : ℕ)
        (sel : (V → ℕ) → Ty → V × V),
        1 < Fintype.card V → (∀ τ, (P τ).Nonempty) → (∀ τ, (D τ).Nonempty) →
        (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) →
        0 < T → (∀ t < T, IsRate (phi t)) → (∀ t < T, 0 < alphaConn P D (phi t)) →
        VariesSlowly phi T eta →
        c * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N ≤ (K : ℝ) →
        ∀ hsel : IsArgmaxSel P D w (fMBP (Fintype.card V)) K sel,
        ∀ π : Policy P D, ∀ q ∈ StateSpace V K, ∀ q' ∈ StateSpace V K,
          (expPayoff w phi π T q
              - expPayoff w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) T q') / T
            ≤ C * (Fintype.card V : ℝ) * ((K : ℝ) / T + Real.sqrt (eta * K))
              + C * (Fintype.card V : ℝ) ^ 2 / K := by sorry

end MirrorBP.JEA
