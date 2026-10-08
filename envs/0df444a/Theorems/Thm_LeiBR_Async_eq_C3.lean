-- Prove2me | Theorems.Thm_LeiBR_Async_eq_C3
-- name    : LeiBR.Async.eq_C3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:09:18.521294+00:00
-- url     : https://prove2.me/theorems/f63b572c-6342-48fa-9d43-2a322f2935c6
-- title:
--   (C.3) — outdated information inside a window: $\max_j \mathbb E\|x_{j,k-\tau_{ij}(k)} - x^*_j\| \le (C+k)\rho^{\max\{0,p-n_0\}}$
-- statement:
--   Let $\rho \in (0,1)$, let the schedule $(I_k)$ and the delays $\tau_{ij}(k) \le k$ satisfy Assumption 4 with constants $B_1, B_2$, and let $n_0 = \lceil B_2/B_1\rceil$. Suppose that, for some $\bar k$, the bound (41) holds at every time up to $\bar k$:
--   $$\mathbb E\big[\|x_{j,k} - x^*_j\|\big] \le (C + k)\,\rho^{\lfloor k/B_1\rfloor}\qquad\text{for all } k \le \bar k \text{ and all } j .$$
--   Let $p = \lfloor \bar k/B_1\rfloor$. Then for every $k \in [pB_1, \bar k]$ and every player $i \in I_k$,
--   $$\max_j \mathbb E\big[\|x_{j,k-\tau_{ij}(k)} - x^*_j\|\big] \le (C + k)\,\rho^{\max\{0,\,p-n_0\}} .$$
--
--   This is the step of the induction proving (41) that absorbs the bounded delays: information at most $B_2 \le n_0B_1$ steps old is at most $n_0$ windows behind.
--
--   **Formalization Note** The statement concerns any random sequence of profiles and any $\rho \in (0,1)$; in the paper $\rho$ is the constant of Lemma 7 and the sequence is Algorithm 3's. The exponent $\max\{0, p - n_0\}$ is natural-number subtraction `p - n0`, and $\lfloor\cdot\rfloor$ is natural-number division.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 33, App. C, (C.3) (with p. 34, (C.4)–(C.5))

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Algorithm

namespace LeiBR.Async

open MeasureTheory

/-- Inequality (C.3) (App. C, p. 33), the delayed-information step of the induction proving (41).
Let `ρ ∈ (0, 1)`, let the delays satisfy `τ_ij(k) ≤ k` and Assumption 4, and suppose (41) holds up to
time `k̄`: `E‖x_{j,k} − x*_j‖ ≤ (C + k) ρ^{⌊k/B₁⌋}` for all `k ≤ k̄` and all `j`. With `p = ⌊k̄/B₁⌋` and
`n₀ = ⌈B₂/B₁⌉`, for every `k ∈ [pB₁, k̄]` and every `i ∈ I_k`,
`max_j E‖x_{j,k−τ_ij(k)} − x*_j‖ ≤ (C + k) ρ^{max{0, p − n₀}}`. -/
theorem eq_C3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ} {n : Fin N → ℕ}
    (x : ℕ → Ω → LeiBR.Sync.Profile n) (xs : LeiBR.Sync.Profile n) (I : ℕ → Finset (Fin N))
    (τ : Fin N → Fin N → ℕ → ℕ) (B1 B2 : ℕ) (hA4 : Assumption4 I τ B1 B2)
    (hτk : ∀ i j k, τ i j k ≤ k) (C ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (kbar : ℕ)
    (hind : ∀ k ≤ kbar, ∀ j, ∫ ω, ‖x k ω j - xs j‖ ∂P ≤ (C + k) * ρ ^ (k / B1)) :
    ∀ k, (kbar / B1) * B1 ≤ k → k ≤ kbar → ∀ i ∈ I k,
      (⨆ j, ∫ ω, ‖x (k - τ i j k) ω j - xs j‖ ∂P) ≤
        (C + k) * ρ ^ (kbar / B1 - nZero B1 B2) := by sorry

end LeiBR.Async
