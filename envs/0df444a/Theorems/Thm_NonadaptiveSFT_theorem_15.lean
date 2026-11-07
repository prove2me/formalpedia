-- Prove2me | Theorems.Thm_NonadaptiveSFT_theorem_15
-- name    : NonadaptiveSFT.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:40.303811+00:00
-- url     : https://prove2.me/theorems/50d7cb13-3021-47f8-9f02-b9d461deb194
-- title:
--   Theorem 15 — recovery at a supplied tail bound: $|\mathrm{supp}\,\widetilde X|<17s$, $\|\widehat X-\widetilde X\|_\infty\le\tau/2$ w.p. $9/10$ with $\min\{N,Cs\log N\log s\}$ nonadaptive queries
-- statement:
--   Let $2\le s<N$ and $\tau\ge0$, and suppose $\sigma_s(\widehat X)_2^2\le s\tau^2$ (33). There is a randomized algorithm with nonadaptive sampling which, taking $s$ and $\tau$ as inputs, with probability at least $9/10$ returns $\widetilde X$ with
--
--   $$|\mathrm{supp}(\widetilde X)|<17s,\qquad\|\widehat X-\widetilde X\|_\infty\le\tau/2.\tag{34}$$
--
--   It uses at most $\min\{N,Cs\log N\log s\}$ point queries (35), for an absolute constant $C$, and at most $O(s^{7/2}(\log N)^{9/4}\log(s\log N))$ exact operations.
--
--   The main theorem is obtained from it by choosing $s$ and $\tau$ from $k$, $\varepsilon$ and $B$ and hard-thresholding the output.
--
--   **Formalization Note** One admissible program of the machine for all $a,d,s,\tau$, with $X$ as its query oracle; one absolute constant for both bounds; $\log N=ad$. The operation bound holds on every tape.
--
--   Differences from the source:
--   - encoding: a randomized algorithm with nonadaptive sampling → one admissible program of NonadaptiveSFT.Machine with X as its point-query oracle; on a fixed tape the query log at halt is the same for every signal X′; reason: the paper's exact arithmetic model and nonadaptive query model
--   - reading: uses at most min{N, Cs log N log s} queries and O(s^{7/2}(log N)^{9/4} log(s log N)) operations → on every coin tape; reason: worst-case bounds; the proof bounds every execution, including aborts (p.45)
--   - encoding: an absolute constant C and the hidden constant of O(·) → one absolute constant C for both; reason: the larger of two constants serves both
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Theorem 15, p.33 (PDF p.35); proof, pp.45–46 (PDF pp.47–48)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Machine

namespace NonadaptiveSFT

/-- **Theorem 15** (Recovery at a supplied tail-norm upper bound), p.33 (PDF p.35).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

Let `2 ≤ s < N`, `τ ≥ 0`, and suppose `σ_s(X̂)₂² ≤ sτ²` (33). There is a randomized algorithm with
nonadaptive sampling which, taking `s` and `τ` as inputs, with probability at least `9/10` returns
`X̃` with `|supp(X̃)| < 17s` and `‖X̂ − X̃‖_∞ ≤ τ/2` (34). It uses at most `min{N, Cs log N log s}` (35)
point queries, for an absolute constant `C`, and at most `O(s^{7/2}(log N)^{9/4} log(s log N))` exact
operations.

**Formalization Note.** The algorithm is one admissible program of `NonadaptiveSFT.Machine`, the same
for every `a`, `d`, `s`, `τ`; the signal `X` is its point-query oracle. Input:
`NonadaptiveSFT.recoveryInit a d s τ` (integers `a, d, s`; reals `τ`, `cos(2π/2^a)`, `sin(2π/2^a)`);
output: the decoded list `0`. One absolute `C` serves both the query bound and the `O(·)` of the
operation bound. `log = log₂`, `log N = a·d`.
* On every tape the run halts within `C·s^{7/2}(ad)^{9/4}log₂(s·ad)` steps (the bound holds "on every
  execution, including executions that abort", p.45).
* On every tape a halted run has made at most `2^{ad}` and at most `C·s·ad·log₂ s` queries.
* Nonadaptivity: on a fixed tape, the query log at halt is the same for every signal `X'`.
* A measurable set of tapes of probability at least `9/10` on which the output satisfies (34).
`τ = 0` is included. -/
theorem theorem_15 :
    ∃ (P : Program) (_ : Admissible P) (C : ℝ), 0 < C ∧
      ∀ (a d : ℕ), 1 ≤ a → 1 ≤ d → ∀ (s : ℕ), 2 ≤ s → s < 2 ^ (a * d) →
      ∀ (τ : ℝ), 0 ≤ τ → ∀ X : G a d → ℂ, sigma (lexKey a d) s (hat X) ^ 2 ≤ s * τ ^ 2 →
        let L : ℝ := (a * d : ℕ)
        let s₀ := recoveryInit a d s τ
        (∀ ω : ℕ → Bool, ∃ n : ℕ, (run P X s₀ ω n).halted = true ∧
          ((run P X s₀ ω n).work : ℝ) ≤
            C * (s : ℝ) ^ (7 / 2 : ℝ) * L ^ (9 / 4 : ℝ) * Real.logb 2 (s * L)) ∧
        (∀ (ω : ℕ → Bool) (n : ℕ), (run P X s₀ ω n).halted = true →
          (run P X s₀ ω n).queries ≤ 2 ^ (a * d) ∧
          ((run P X s₀ ω n).queries : ℝ) ≤ C * s * L * Real.logb 2 s) ∧
        (∀ (X' : G a d → ℂ) (ω : ℕ → Bool) (n n' : ℕ), (run P X s₀ ω n).halted = true →
          (run P X' s₀ ω n').halted = true →
          (run P X s₀ ω n).queryLog = (run P X' s₀ ω n').queryLog) ∧
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ (9 / 10 : ENNReal) ≤ coinTape E ∧
          ∀ ω ∈ E, ∀ n : ℕ, (run P X s₀ ω n).halted = true →
            suppCard (outVec (run P X s₀ ω n) 0) < 17 * s ∧
            linf (hat X - outVec (run P X s₀ ω n) 0) ≤ τ / 2 := by sorry

end NonadaptiveSFT
