-- Prove2me | Theorems.Thm_MirrorBP_JEA_proposition_2
-- name    : MirrorBP.JEA.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:49.948331+00:00
-- url     : https://prove2.me/theorems/f59c040c-ea9b-45c9-a202-b93abd5ad580
-- title:
--   Proposition 2, p. 16 — L_T^MBP ≤ CmK/Δ_T + Cm²/K + Δ_T mη for every batch size 0 < Δ_T < T, once K ≥ poly(m, 1/α_min)
-- statement:
--   There are a universal constant $C$ and a polynomial bound $K_1 = c\,(m + 1/\alpha_{\min})^N$ such that the following holds. Consider the setting of Theorem 1: $V$ a finite set of $m > 1$ nodes, a finite type set with nonempty $\mathcal P(\tau), \mathcal D(\tau)$, $|w_{j\tau k}| \le 1$, a horizon $T \ge 1$, rate vectors $\boldsymbol\phi^0,\dots,\boldsymbol\phi^{T-1}$ satisfying Condition 1 and varying $\eta$-slowly, $\alpha_{\min} = \min_{t<T}\alpha(\boldsymbol\phi^t)$. For every $K \ge K_1$ and every integer $0 < \Delta_T < T$, MBP with the congestion function (8) and any argmax tie-break satisfies, for every feasible policy $\pi$ and all initial states $\mathbf q, \mathbf q' \in \Omega_K$,
--   $$\frac1T\sum_{t=0}^{T-1}\mathbb E[v^\pi[t]\mid\mathbf q[0]=\mathbf q] - \frac1T\sum_{t=0}^{T-1}\mathbb E[v^{\mathrm{MBP}}[t]\mid\mathbf q[0]=\mathbf q'] \le M_1\frac{K}{\Delta_T} + M_2\frac1K + \Delta_T m\eta, \qquad M_1 = Cm,\ M_2 = Cm^2;$$
--   that is, $L^{\mathrm{MBP}}_T \le M_1 K/\Delta_T + M_2/K + \Delta_T m\eta$.
--
--   The batch size $\Delta_T$ is a device of the analysis, not of the policy; Theorem 1 follows by choosing $\Delta_T$.
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
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, p. 16, Proposition 2

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem proposition_2 :
    ∃ C : ℝ, ∃ c : ℝ, ∃ N : ℕ,
      ∀ (V Ty : Type) [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
        (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (T : ℕ) (eta : ℝ) (K : ℕ)
        (sel : (V → ℕ) → Ty → V × V) (ΔT : ℕ),
        1 < Fintype.card V → (∀ τ, (P τ).Nonempty) → (∀ τ, (D τ).Nonempty) →
        (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) →
        0 < T → (∀ t < T, IsRate (phi t)) → (∀ t < T, 0 < alphaConn P D (phi t)) →
        VariesSlowly phi T eta →
        c * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N ≤ (K : ℝ) →
        0 < ΔT → ΔT < T →
        ∀ hsel : IsArgmaxSel P D w (fMBP (Fintype.card V)) K sel,
        ∀ π : Policy P D, ∀ q ∈ StateSpace V K, ∀ q' ∈ StateSpace V K,
          (expPayoff w phi π T q
              - expPayoff w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) T q') / T
            ≤ C * (Fintype.card V : ℝ) * ((K : ℝ) / ΔT) + C * (Fintype.card V : ℝ) ^ 2 / K
              + ΔT * (Fintype.card V : ℝ) * eta := by sorry

end MirrorBP.JEA
