-- Prove2me | Theorems.Thm_GravesWillems_Serial_expected_backlog_transfer_bounds
-- name    : GravesWillems.Serial.expected_backlog_transfer_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:19:42.267988+00:00
-- url     : https://prove2.me/theorems/ff79220d-729a-478d-9a7c-ba11ad1d91ae
-- title:
--   Proof of the Result — expected backlogs after moving $\Delta$ of base stock from stage $k$ to $k+1$
-- statement:
--   Let $(\Omega, \mu)$ be a probability space and $d(\omega, \cdot)$ a random end-item demand path with $d(\cdot, \tau)$ integrable for every period $\tau \in \mathbb{Z}$. Consider the $N$-stage serial base-stock system with lead times $T_i \in \mathbb{N}$ and arbitrary real base stocks $B^*$. Fix $1 \le k < N$ and $\Delta \ge 0$, and let $B^{**}$ equal $B^*$ except $B^{**}_k = B^*_k - \Delta$ and $B^{**}_{k+1} = B^*_{k+1} + \Delta$. Write $E[Q_i]^*$ and $E[Q_i]^{**}$ for the expected backlog $E[Q_i(t)]$ at stage $i$ in a period $t$ under the two vectors. Then for every period $t$ and every stage $i \in \{1, \dots, N\}$:
--   $$\begin{aligned}
--   E[Q_i]^{**} &= E[Q_i]^* && \text{for } i > k+1,\\
--   E[Q_i]^* \le E[Q_i]^{**} &\le E[Q_i]^* + \Delta && \text{for } i < k+1,\\
--   E[Q_{k+1}]^* \ge E[Q_{k+1}]^{**} &\ge E[Q_{k+1}]^* - \Delta. &&
--   \end{aligned}$$
--
--   These bounds are what allow the echelon-weighted backlog part of the objective of $\mathbf P^*$ to rise by at most $e_k \Delta$ under the transfer (Eq. (A8)).
--
--   **Formalization Note** The paper has $\Delta > 0$ from the context of the proof; the statement here allows $\Delta \ge 0$ and any base stocks (feasibility is not needed). Expectations are Bochner integrals at a fixed period $t$; integrability of the backlog is not assumed and follows from integrability of each period's demand.
-- source:
--   Graves and Willems, Optimizing Strategic Safety Stock Placement in Supply Chains, Manufacturing & Service Operations Management 2(1), 2000, p. 82, Appendix, proof of the Result (bounds on E[Q_i]** derived from Eq. (A2))

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP
open MeasureTheory

namespace GravesWillems.Serial

/-- Appendix, proof of the Result (Graves–Willems 2000, p. 82): moving `Δ ≥ 0` units of base
stock from stage `k` to stage `k + 1` (`1 ≤ k < N`) changes the expected backlogs at any period
`t` as follows: `E[Qᵢ]** = E[Qᵢ]*` for `i > k + 1`; `E[Qᵢ]* ≤ E[Qᵢ]** ≤ E[Qᵢ]* + Δ` for
`i < k + 1`; and `E[Q_{k+1}]* ≥ E[Q_{k+1}]** ≥ E[Q_{k+1}]* − Δ`. The base stocks `B` are
arbitrary; the demand in every period is integrable. -/
theorem expected_backlog_transfer_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (N : ℕ) (T : ℕ → ℕ) (B : ℕ → ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k + 1 ≤ N)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (t : ℤ) :
    (∀ i ∈ Finset.Icc 1 N, k + 1 < i →
      ∫ ω, backlog N T (transfer B k Δ) (d ω) i t ∂μ = ∫ ω, backlog N T B (d ω) i t ∂μ) ∧
    (∀ i ∈ Finset.Icc 1 N, i < k + 1 →
      ∫ ω, backlog N T B (d ω) i t ∂μ ≤ ∫ ω, backlog N T (transfer B k Δ) (d ω) i t ∂μ ∧
      ∫ ω, backlog N T (transfer B k Δ) (d ω) i t ∂μ ≤ ∫ ω, backlog N T B (d ω) i t ∂μ + Δ) ∧
    (∫ ω, backlog N T (transfer B k Δ) (d ω) (k + 1) t ∂μ
        ≤ ∫ ω, backlog N T B (d ω) (k + 1) t ∂μ ∧
      ∫ ω, backlog N T B (d ω) (k + 1) t ∂μ - Δ
        ≤ ∫ ω, backlog N T (transfer B k Δ) (d ω) (k + 1) t ∂μ) := by sorry

end GravesWillems.Serial
