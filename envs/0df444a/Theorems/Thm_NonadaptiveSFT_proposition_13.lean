-- Prove2me | Theorems.Thm_NonadaptiveSFT_proposition_13
-- name    : NonadaptiveSFT.proposition_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:39.644088+00:00
-- url     : https://prove2.me/theorems/dafb4b55-7882-4042-9d40-4e57acb245da
-- title:
--   Proposition 13 — the complete norm-bounded locator: heavy frequencies w.p. $1-\gamma$ with $O(\kappa\log N\log(2\kappa)+\kappa\log(\kappa\log N/\gamma))$ nonadaptive queries
-- statement:
--   Let $\|\widehat R\|_2\le M$, $0<T\le M$, $\kappa=M^2/T^2$ and $0<\gamma<1/2$. There is a randomized algorithm, with point-query access to $R$, which with probability at least $1-\gamma$ returns a list containing every $f$ with $|\widehat R(f)|\ge T$ and only frequencies with $|\widehat R(f)|>T/2$. It makes
--
--   $$O\big(\kappa(\log N)\log(2\kappa)+\kappa\log(\kappa(\log N)/\gamma)\big)$$
--
--   nonadaptive point queries, counting repetitions, and on every execution, including executions that abort, its running time and space usage are bounded by a fixed polynomial in $\kappa$, $\log N$ and $\gamma^{-1}$.
--
--   The locator is the search engine of the recovery algorithm: each call finds the frequencies of the current residual above a threshold.
--
--   **Formalization Note** One admissible program of the machine for all $a,d$, with $R$ as its query oracle and inputs $a,d,M,T,\gamma$ and the root of unity; the constants are absolute; $\log N=ad$.
--
--   Differences from the source:
--   - encoding: there exists a random algorithm → one admissible program of NonadaptiveSFT.Machine, the same for every a, d, with R as its point-query oracle; reason: the paper's exact arithmetic model (§2.3)
--   - encoding: nonadaptive point queries → on a fixed coin tape, the query log at halt is the same for every oracle R′; reason: query locations chosen in advance from randomness alone
--   - encoding: running time and space usage bounded by a fixed polynomial in κ, log N, γ⁻¹ → work ≤ C(κ·ad/γ)^K on every tape; space is not stated separately; reason: κ, ad, 1/γ ≥ 1, so every polynomial in them is bounded by such a monomial; each step writes at most one memory cell, so space ≤ work
--   - reading: with probability at least 1 − γ, returns a list … → a measurable set of tapes of probability ≥ 1 − γ on which a halted run has not aborted and its list has both properties; reason: an aborted run returns no list
--   - encoding: O(·) → an absolute constant C chosen before all the data; reason: the meaning of O(·)
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Proposition 13, p.27 (PDF p.29); running time, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Machine

namespace NonadaptiveSFT

/-- **Proposition 13** (Complete norm-bounded locator), p.27 (PDF p.29).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

Let `‖R̂‖₂ ≤ M`, `0 < T ≤ M`, `κ = M²/T²`, `0 < γ < 1/2`. There exists a random algorithm that, with
probability at least `1 − γ`, returns a list containing every `f` with `|R̂(f)| ≥ T` and only
frequencies with `|R̂(f)| > T/2`. It makes `O(κ(log N) log(2κ) + κ log(κ(log N)/γ))` nonadaptive point
queries, counting repetitions. On every execution, including executions that terminate with an
abort, its running time and space usage are bounded by a fixed polynomial in `κ`, `log N`, `γ^{−1}`.

**Formalization Note.** The algorithm is one admissible program of `NonadaptiveSFT.Machine`, the same
for every `a`, `d`; the residual `R` is its point-query oracle ("The test at v uses point queries to
R", p.27). Input: `NonadaptiveSFT.locatorInit a d M T γ`. Output on halt: the abort flag and the
frequency list `0`. `C`, `K` are absolute. `log = log₂`, `log N = a·d`.
* On every tape the run halts with `work ≤ C(κ·ad/γ)^K` (a fixed polynomial in `κ`, `log N`, `1/γ`,
  all `≥ 1`). Space: every step writes at most one memory cell, so the cells written are bounded by
  the same polynomial.
* On every tape a halted run has made at most `C(κ·ad·log₂(2κ) + κ·log₂(κ·ad/γ))` queries.
* Nonadaptivity: on a fixed tape, the query log at halt is the same for every oracle `R'`.
* A measurable set of tapes of probability at least `1 − γ` on which a halted run has not aborted
  and its list contains every `f` with `|R̂(f)| ≥ T` and only `f` with `|R̂(f)| > T/2`. -/
theorem proposition_13 :
    ∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (a d : ℕ), 1 ≤ a → 1 ≤ d → ∀ (R : G a d → ℂ) (M T γ : ℝ),
        l2 (hat R) ≤ M → 0 < T → T ≤ M → 0 < γ → γ < 1 / 2 →
        let κ : ℝ := M ^ 2 / T ^ 2
        let L : ℝ := (a * d : ℕ)
        let s₀ := locatorInit a d M T γ
        (∀ ω : ℕ → Bool, ∃ n : ℕ, (run P R s₀ ω n).halted = true ∧
          ((run P R s₀ ω n).work : ℝ) ≤ C * (κ * L / γ) ^ K) ∧
        (∀ (ω : ℕ → Bool) (n : ℕ), (run P R s₀ ω n).halted = true →
          ((run P R s₀ ω n).queries : ℝ) ≤
            C * (κ * L * Real.logb 2 (2 * κ) + κ * Real.logb 2 (κ * L / γ))) ∧
        (∀ (R' : G a d → ℂ) (ω : ℕ → Bool) (n n' : ℕ), (run P R s₀ ω n).halted = true →
          (run P R' s₀ ω n').halted = true →
          (run P R s₀ ω n).queryLog = (run P R' s₀ ω n').queryLog) ∧
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ ENNReal.ofReal (1 - γ) ≤ coinTape E ∧
          ∀ ω ∈ E, ∀ n : ℕ, (run P R s₀ ω n).halted = true →
            ¬ aborted (run P R s₀ ω n) ∧
            (∀ f, T ≤ ‖hat R f‖ → f ∈ outFreqs (run P R s₀ ω n) 0) ∧
            (∀ f ∈ outFreqs (run P R s₀ ω n) 0, T / 2 < ‖hat R f‖) := by sorry

end NonadaptiveSFT
