-- Prove2me | Theorems.Thm_MirrorBP_JEA_proposition_4
-- name    : MirrorBP.JEA.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:32.729774+00:00
-- url     : https://prove2.me/theorems/c8bdcae0-e218-41ca-b08f-48252d62851b
-- title:
--   Proposition 4, p. 20 — variation gap (1/T)Σ_t W^SPP(φᵗ) ≥ W^SPP(φ̄) − mηT for η-slowly varying rates
-- statement:
--   Throughout, $V$ is a finite set of $m = |V| > 1$ nodes, $\mathcal T$ a finite set of demand types, each type $\tau$ has nonempty pick-up and drop-off neighborhoods $\mathcal P(\tau), \mathcal D(\tau) \subseteq V$, and the payoffs satisfy $|w_{j\tau k}| \le 1$ for $j \in \mathcal P(\tau)$, $k \in \mathcal D(\tau)$.
--
--   Let $T \ge 1$, $\eta \ge 0$, and let $\boldsymbol\phi^0, \dots, \boldsymbol\phi^{T-1}$ be rate vectors varying $\eta$-slowly (Definition 1). Then
--   $$\frac1T\sum_{t=0}^{T-1} W^{\mathrm{SPP}}(\boldsymbol\phi^t) \ge W^{\mathrm{SPP}}(\bar{\boldsymbol\phi}) - m\eta T, \qquad \bar{\boldsymbol\phi} = \frac1T\sum_{t<T}\boldsymbol\phi^t.$$
--
--   This bounds the loss from replacing a time-varying demand by its average, the variation-gap term of Proposition 2.
--
--   Differences from the source:
--   - generalization: max_{τ, j ∈ P(τ), k ∈ D(τ)} |w_{jτk}| = 1 → |w j τ k| ≤ 1 for j ∈ P τ, k ∈ D τ; reason: the scaling is 'without loss of generality' (p. 10); every instance with max |w| = 1 satisfies |w| ≤ 1.
--   - reading: type set 𝒯 (finiteness implicit) → [Fintype Ty]; reason: the model is 'a finite-state Markov chain' and SPP 'a linear program' with sums over 𝒯 (pp. 9, 15); Appendix C's remark on infinitely many types presupposes finitely many in the model.
--   - encoding: periods t = 1, …, T in (4) and Definition 1 (0, …, T−1 elsewhere) → periods t = 0, …, T − 1 with rates phi t and start state q[0]; reason: the paper mixes both conventions; same instances after an index shift.
--   - encoding: (1/(T−1)) Σ_{t=1}^{T−1} ‖φ^{t+1} − φ^t‖₁ ≤ η → Σ_{t<T−1} Σ_τ |phi (t+1) τ − phi t τ| ≤ (T − 1) η; reason: multiplied out by T − 1; identical for T ≥ 2, and the paper's expression is undefined for T = 1.
--   - encoding: horizon T (with 1/T) → 0 < T; reason: excludes T = 0, where 1/T is undefined.
--   - generalization: for some η > 0 → η ≥ 0; reason: η = 0 is included; for T ≥ 2 Definition 1 forces η ≥ 0 anyway.
--   - encoding: 'For any 0 ≤ t ≤ T − 1 we have' → no free t; reason: the displayed inequality (20) has no free t; the phrase binds nothing.
--   - encoding: (1/T) Σ_{t=1}^{T} W^SPP(φ_t) → (1/T) Σ_{t<T} Wspp (phi t); reason: the T periods of the horizon under the 0-based convention, the same periods as in φ̄.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, p. 20, Proposition 4, (20); Appendix C, appendix pp. 13–14 (PDF 46–47)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem proposition_4 {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (phi : ℕ → Ty → ℝ) (T : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (hT : 0 < T) (hrate : ∀ t < T, IsRate (phi t))
    (hvar : VariesSlowly phi T eta) :
    Wspp P D w (phibar phi T) - (Fintype.card V : ℝ) * eta * T
      ≤ (1 / (T : ℝ)) * ∑ t ∈ range T, Wspp P D w (phi t) := by sorry

end MirrorBP.JEA
