-- Prove2me | Theorems.Thm_MirrorBP_JEA_proposition_1
-- name    : MirrorBP.JEA.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:33.152302+00:00
-- url     : https://prove2.me/theorems/6ecef88e-565c-4756-a6f1-5ad593e55ee8
-- title:
--   Proposition 1, p. 16 — W*_T ≤ W^SPP(φ̄) + mK/T, and W* ≤ limsup_T W^SPP(φ̄_T)
-- statement:
--   Throughout, $V$ is a finite set of $m = |V| > 1$ nodes, $\mathcal T$ a finite set of demand types, each type $\tau$ has nonempty pick-up and drop-off neighborhoods $\mathcal P(\tau), \mathcal D(\tau) \subseteq V$, and the payoffs satisfy $|w_{j\tau k}| \le 1$ for $j \in \mathcal P(\tau)$, $k \in \mathcal D(\tau)$.
--
--   Let $(\boldsymbol\phi^t)_{t \ge 0}$ be rate vectors and $K \in \mathbb N$.
--
--   1. For every horizon $T \ge 1$, every feasible policy $\pi$ and every starting state $\mathbf q[0] \in \Omega_K$,
--   $$\frac1T \sum_{t=0}^{T-1}\mathbb E[v^\pi[t] \mid \mathbf q[0]] \le W^{\mathrm{SPP}}(\bar{\boldsymbol\phi}_T) + m\frac KT, \qquad \bar{\boldsymbol\phi}_T = \frac1T\sum_{t<T}\boldsymbol\phi^t;$$
--   equivalently $W^*_T \le W^{\mathrm{SPP}}(\bar{\boldsymbol\phi}_T) + mK/T$.
--   2. $$W^* = \limsup_{T\to\infty} W^*_T \le \limsup_{T\to\infty} W^{\mathrm{SPP}}(\bar{\boldsymbol\phi}_T).$$
--
--   For stationary rates $\boldsymbol\phi^t \equiv \boldsymbol\phi$ the second clause is $W^* \le W^{\mathrm{SPP}}(\boldsymbol\phi)$. The proposition bounds the benchmark of Theorem 1 by a static LP.
--
--   Differences from the source:
--   - generalization: max_{τ, j ∈ P(τ), k ∈ D(τ)} |w_{jτk}| = 1 → |w j τ k| ≤ 1 for j ∈ P τ, k ∈ D τ; reason: the scaling is 'without loss of generality' (p. 10); every instance with max |w| = 1 satisfies |w| ≤ 1.
--   - reading: type set 𝒯 (finiteness implicit) → [Fintype Ty]; reason: the model is 'a finite-state Markov chain' and SPP 'a linear program' with sums over 𝒯 (pp. 9, 15); Appendix C's remark on infinitely many types presupposes finitely many in the model.
--   - generalization: a policy maps the history of types and states (τ[t′], q[t′])_{t′≤t} to a randomized decision → Policy: (period, past (state, type, decision) triples, current state, current type) ↦ probability vector on feasible decisions; reason: the class contains every policy of 𝒰, so the benchmark W*_T can only grow; MBP belongs to both classes.
--   - encoding: periods t = 1, …, T in (4) and Definition 1 (0, …, T−1 elsewhere) → periods t = 0, …, T − 1 with rates phi t and start state q[0]; reason: the paper mixes both conventions; same instances after an index shift.
--   - encoding: E[v^π[t] | q[0] = q] over the random arrivals and decisions → expPayoff, the finite recursion over types and decisions; reason: each period has finitely many outcomes; the recursion is the law of the controlled chain.
--   - encoding: W*_T ≤ W^SPP(φ̄) + mK/T → ∀ T > 0, ∀ π, ∀ q ∈ Ω_K, expPayoff π T q / T ≤ Wspp (phibar phi T) + mK/T; reason: the same inequality without a real sSup.
--   - reading: W* ≤ W^SPP(φ̄) → Wstar ≤ limsup_T Wspp (phibar phi T); reason: φ̄ depends on T while W* is a limsup in T; this reading equals W^SPP(φ) for stationary rates and is never weaker than that case.
--   - encoding: rates {φᵗ} on the horizon → phi : ℕ → Ty → ℝ with every phi t a probability vector; reason: W* is a limit over all horizons, so the whole sequence is needed.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, p. 16, Proposition 1, (14)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem proposition_1 {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (phi : ℕ → Ty → ℝ) (K : ℕ) (hrate : ∀ t, IsRate (phi t)) :
    (∀ T : ℕ, 0 < T → ∀ π : Policy P D, ∀ q ∈ StateSpace V K,
        expPayoff w phi π T q / T ≤ Wspp P D w (phibar phi T) + (Fintype.card V : ℝ) * K / T) ∧
      Wstar P D w phi K ≤ Filter.limsup (fun T : ℕ => Wspp P D w (phibar phi T)) Filter.atTop := by sorry

end MirrorBP.JEA
