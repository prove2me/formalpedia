-- Prove2me | Theorems.Thm_NetworkControl_Backpressure_lemma_lyapunov_stability_T_slot
-- name    : NetworkControl.Backpressure.lemma_lyapunov_stability_T_slot
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-21T06:22:29.855367+00:00
-- url     : https://prove2.me/theorems/6a87cbe0-6258-4a98-8b8a-c19bdd0867b3
-- title:
--   Lemma 4.2 — T-slot Lyapunov drift
-- statement:
--   **Lemma 4.2** (p. 52). If there is a positive integer $T$ such that $\mathbb E\{U(\tau)\}<\infty$
--   for $\tau\in\{0,\dots,T-1\}$, and if there are positive $B,\varepsilon$ such that at every
--   timeslot $t_0$ the conditional expected $T$-slot drift of $L(U(t))$ given $U(t_0)$ satisfies
--   $\mathbb E\{L(U(t_0+T))-L(U(t_0))\mid U(t_0)\}\le B-\varepsilon\sum_i U_i(t_0)$, then the
--   network is strongly stable and $\limsup_{t\to\infty}\frac1t\sum_\tau\sum_i\mathbb E\{U_i(\tau)\}
--   \le B/\varepsilon$ — the same conclusion as Lemma 4.1, with the drift measured over a
--   $T$-slot block instead of one. The book states its proof "is similar to the proof of Lemma
--   4.1, and is omitted for brevity" (p. 52).
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 52, Lemma 4.2

import Mathlib
import Definitions.Def_NetworkControl_Backpressure_StronglyStable
import Definitions.Def_NetworkControl_Backpressure_lyapunovL

namespace NetworkControl.Backpressure

open MeasureTheory

/-- Lemma 4.2 (T-slot Lyapunov drift), p. 52. If there is a positive integer `T` such that
`E{U(τ)} < ∞` for `τ ∈ {0,…,T-1}`, and if there are positive `B, ε` such that at every timeslot
`t0` the conditional expected `T`-slot drift of `L(U(t))` given `U(t0)` satisfies
`E{L(U(t0+T)) - L(U(t0)) | U(t0)} ≤ B - ε Σ_i U_i(t0)`, then the network is strongly stable and
`limsup_{t→∞} (1/t) Σ_τ Σ_i E{U_i(τ)} ≤ B/ε` — the same conclusion as Lemma 4.1, with the drift
measured over a `T`-slot block instead of one.

**Formalization note.** `hIntegInit` is the book's own literal initial-segment hypothesis
(`E{U(τ)}<∞` for `τ<T`); `hIntegU` is an additional guard (not itself in the book's statement)
needed so `∫ ω, U t ω i ∂P` is non-junk at every `t`, matching the pattern used throughout this
series (`03-capacity-region`'s `Integrable` guards, Faithfulness trap 2). The `limsup` conclusion
is stated in the same quantifier-light form as Lemma 4.1. -/
theorem lemma_lyapunov_stability_T_slot
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {L : ℕ} (U : ℕ → Ω → Fin L → ℝ) (T : ℕ) (hT : 0 < T) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hIntegInit : ∀ τ : ℕ, τ < T → ∀ i : Fin L, Integrable (fun ω => U τ ω i) P)
    (hMeas : ∀ t : ℕ, ∀ i : Fin L, Measurable (fun ω => U t ω i))
    (hIntegU : ∀ t : ℕ, ∀ i : Fin L, Integrable (fun ω => U t ω i) P)
    (hIntegDrift : ∀ t0 : ℕ,
      Integrable (fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω)) P)
    (hdrift : ∀ t0 : ℕ,
      (P[(fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω))
          | MeasurableSpace.comap (U t0) inferInstance])
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin L, U t0 ω i)) :
    NetworkStronglyStable (fun i t => ∫ ω, U t ω i ∂P) ∧
      ∀ t : ℕ, (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin L, ∫ ω, U τ ω i ∂P ≤ B / ε := by sorry

end NetworkControl.Backpressure
