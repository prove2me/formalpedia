-- Prove2me | Theorems.Thm_MirrorBP_JEA_proposition_3
-- name    : MirrorBP.JEA.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:50.043885+00:00
-- url     : https://prove2.me/theorems/a8c9e058-d6f0-4106-951c-9b3cd95f4216
-- title:
--   Proposition 3, p. 17 — the policy gap (1/T)Σ_t W^SPP(φᵗ) − W_T^MBP ≤ CmK/T + Cm²/K for K ≥ poly(m, 1/α_min)
-- statement:
--   There are a universal constant $C$ and a polynomial bound $K_1 = c\,(m + 1/\alpha_{\min})^N$ such that the following holds. Let $V$ be a finite set of $m > 1$ nodes, $\mathcal T$ a finite type set with nonempty $\mathcal P(\tau), \mathcal D(\tau)$, $|w_{j\tau k}| \le 1$, $T \ge 1$, and $\boldsymbol\phi^0,\dots,\boldsymbol\phi^{T-1}$ rate vectors satisfying Condition 1 ($\alpha(\boldsymbol\phi^t) > 0$), with $\alpha_{\min} = \min_{t<T}\alpha(\boldsymbol\phi^t)$. For every $K \ge K_1$, MBP with the congestion function (8) and any argmax tie-break satisfies, for every initial state $\mathbf q' \in \Omega_K$,
--   $$\frac1T\sum_{t=0}^{T-1} W^{\mathrm{SPP}}(\boldsymbol\phi^t) - \frac1T\sum_{t=0}^{T-1}\mathbb E[v^{\mathrm{MBP}}[t] \mid \mathbf q[0] = \mathbf q'] \le M_1\frac KT + M_2\frac1K, \qquad M_1 = Cm,\ M_2 = Cm^2.$$
--   Since $\mathbf q'$ is arbitrary, the second sum may be replaced by $W^{\mathrm{MBP}}_T$ (its minimum over $\mathbf q'$).
--
--   The proposition holds for arbitrary rate sequences satisfying Condition 1; it is the policy-gap part of the proof of Theorem 1.
--
--   Differences from the source:
--   - generalization: max_{τ, j ∈ P(τ), k ∈ D(τ)} |w_{jτk}| = 1 → |w j τ k| ≤ 1 for j ∈ P τ, k ∈ D τ; reason: the scaling is 'without loss of generality' (p. 10); every instance with max |w| = 1 satisfies |w| ≤ 1.
--   - reading: type set 𝒯 (finiteness implicit) → [Fintype Ty]; reason: the model is 'a finite-state Markov chain' and SPP 'a linear program' with sums over 𝒯 (pp. 9, 15); Appendix C's remark on infinitely many types presupposes finitely many in the model.
--   - encoding: periods t = 1, …, T in (4) and Definition 1 (0, …, T−1 elsewhere) → periods t = 0, …, T − 1 with rates phi t and start state q[0]; reason: the paper mixes both conventions; same instances after an index shift.
--   - encoding: E[v^π[t] | q[0] = q] over the random arrivals and decisions → expPayoff, the finite recursion over types and decisions; reason: each period has finitely many outcomes; the recursion is the law of the controlled chain.
--   - generalization: (j*, k*) = argmax_{j ∈ P(τ), k ∈ D(τ)} of the score → any tie-break sel with IsArgmaxSel; reason: the paper's argmax is some tie-break; the statement holds for every one.
--   - encoding: K₁ = poly(m, 1/α_min), C universal → ∃ C c N before every type and instance binder, K ≥ c (m + 1/α_min)^N; reason: a polynomial in (m, 1/α) with m ≥ 2 is bounded by c (m + 1/α)^N, and conversely; C, c, N do not depend on the instance.
--   - reading: α_min = min_{0≤t≤T} α(φᵗ) → Condition 1 and α_min over the periods t < T; reason: the periods of the horizon under the 0-based convention (Theorem 1 writes 1 ≤ t ≤ T).
--   - encoding: W_T^MBP = min_{q′ ∈ Ω_K} (1/T)Σ E[v^MBP] → ∀ q′ ∈ Ω_K; reason: a bound for every q′ is a bound for the minimum, and conversely.
--   - encoding: horizon T (with 1/T) → 0 < T; reason: excludes T = 0, where 1/T is undefined.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, p. 17, Proposition 3

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem proposition_3 :
    ∃ C : ℝ, ∃ c : ℝ, ∃ N : ℕ,
      ∀ (V Ty : Type) [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
        (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (T K : ℕ)
        (sel : (V → ℕ) → Ty → V × V),
        1 < Fintype.card V → (∀ τ, (P τ).Nonempty) → (∀ τ, (D τ).Nonempty) →
        (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) →
        0 < T → (∀ t < T, IsRate (phi t)) → (∀ t < T, 0 < alphaConn P D (phi t)) →
        c * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N ≤ (K : ℝ) →
        ∀ hsel : IsArgmaxSel P D w (fMBP (Fintype.card V)) K sel,
        ∀ q' ∈ StateSpace V K,
          (1 / (T : ℝ)) * ∑ t ∈ range T, Wspp P D w (phi t)
              - expPayoff w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) T q' / T
            ≤ C * (Fintype.card V : ℝ) * ((K : ℝ) / T) + C * (Fintype.card V : ℝ) ^ 2 / K := by sorry

end MirrorBP.JEA
