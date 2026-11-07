-- Prove2me | Theorems.Thm_NonadaptiveSFT_theorem_1
-- name    : NonadaptiveSFT.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:48.136445+00:00
-- url     : https://prove2.me/theorems/6090d75b-3312-44e6-aace-5487bb7c01c7
-- title:
--   Theorem 1 — nonadaptive $(1+\varepsilon)$ $\ell_2/\ell_2$ sparse Fourier recovery on $(\mathbb Z/2^a\mathbb Z)^d$ from a tail estimate
-- statement:
--   Fix a constant $c\ge1$. Let $a,d\ge1$ be integers, $G=(\mathbb Z/2^a\mathbb Z)^d$, $N=|G|=2^{ad}$, $\varepsilon\in(0,1/2]$ and $2\le k<N$. There is a randomized algorithm which, given point-query access to any fixed $X\in\mathbb C^G$ and a tail estimate $B$ with
--
--   $$\sigma_k(\widehat X)_2\le B\le c\,\sigma_k(\widehat X)_2,$$
--
--   uses nonadaptive queries, computes an estimate $\widetilde X^{pre}$ with $O_c(k/\varepsilon^2)$ nonzero coordinates, and returns the $k$-sparse vector $\widetilde X=H_k(\widetilde X^{pre})$. With probability at least $9/10$, both
--
--   $$\|\widehat X-\widetilde X^{pre}\|_\infty\le\frac\varepsilon{\sqrt k}\,\sigma_k(\widehat X)_2\qquad\text{and}\qquad\|\widehat X-\widetilde X\|_2^2\le(1+\varepsilon)\,\sigma_k(\widehat X)_2^2.\tag{3}$$
--
--   The algorithm makes at most $\min\{N,O((k/\varepsilon^2)(\log N)\log(k/\varepsilon))\}$ queries (4), and its running time with exact operations is
--
--   $$O\Big(\frac{k^{7/2}}{\varepsilon^7}(\log N)^{9/4}\log\frac{k\log N}{\varepsilon}\Big)=\mathrm{poly}((k/\varepsilon)\log N).$$
--
--   The hidden constants may depend on $c$.
--
--   This is the paper's main result: a $(1+\varepsilon)$ guarantee with nonadaptive queries in every dimension, with no assumption on the range of the coefficients or on the signal-to-noise ratio.
--
--   **Formalization Note** The algorithm is one admissible program of the machine (§2.3), taking $a,d,k,\varepsilon,B,c$ and the supplied root of unity as input and $X$ as its query oracle; $X^{pre}$ and $\widetilde X$ are read from two output lists. The constant $C$ depends on $c$ only. $\log=\log_2$ and $\log N=ad$. The work, query and support bounds and $\widetilde X=H_k(\widetilde X^{pre})$ hold on every coin tape; both error bounds hold together on a measurable set of tapes of probability at least $9/10$. $B=0$ (exactly $k$-sparse spectra) is included.
--
--   Differences from the source:
--   - encoding: a randomized algorithm (exact operations, point queries) → an admissible program of NonadaptiveSFT.Machine: real RAM with a ℤ/2^aℤ coordinate bank, fair coins, point queries; complex numbers as pairs of reals; the root of unity supplied as input reals cos(2π/2^a), sin(2π/2^a); reason: the paper's model of §2.3; unit-cost complex arithmetic is O(1) real operations
--   - generalization: Fix a constant c ≥ 1. … There is a randomized algorithm → one program P for every c ≥ 1 (c is an input), then C depending on c; reason: one program for all c specializes to one program per c; Algorithm 1 reads c
--   - encoding: uses non-adaptive queries → on a fixed coin tape, the query log at halt is the same for every signal X′; reason: query locations chosen in advance from randomness alone (p.2)
--   - reading: computes X̃^pre with O_c(k/ε²) nonzero coordinates, returns X̃ = H_k(X̃^pre), at most min{N, …} queries, runtime at most O(…) → on every coin tape; reason: these are stated outside the probability clause; the proof bounds every execution
--   - reading: Fix an order on G (ties of H_k) → the lexicographic order of the coordinate representatives; reason: the page fixes an unspecified order; an algorithm must be able to compare in it, and the lexicographic order is the natural computable one
--   - encoding: O(·) and O_c(·) → one constant C > 0 depending on c only, chosen before a, d, ε, k, X, B; reason: the meaning of O_c(·)
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Theorem 1, p.2 (PDF p.4); restated pp.46–47 (PDF pp.48–49)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Machine

namespace NonadaptiveSFT

/-- **Theorem 1** (Nonadaptive sparse Fourier recovery), p.2 (PDF p.4); restated pp.46–47.

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

"Fix a constant c ≥ 1. Let a, d ≥ 1 be integers, G = (Z/2^aZ)^d, N = |G| = 2^{ad}, ε ∈ (0, 1/2], and
2 ≤ k < N. There is a randomized algorithm which, given point-query access to any fixed X ∈ C^G and a
tail estimate B satisfying σ_k(X̂)₂ ≤ B ≤ c σ_k(X̂)₂, uses non-adaptive queries, computes an estimate
X̃^pre with O_c(k/ε²) nonzero coordinates, and returns the k-sparse vector X̃ = H_k(X̃^pre). With
probability at least 9/10, both ∥X̂ − X̃^pre∥_∞ ≤ (ε/√k) σ_k(X̂)₂ and ∥X̂ − X̃∥₂² ≤ (1 + ε)σ_k(X̂)₂² (3)
… Moreover, the algorithm makes at most min{N, O((k/ε²)(log N) log(k/ε))} (4) queries. The runtime
of the algorithm (assuming exact operations) is at most O((k^{7/2}/ε^7)(log N)^{9/4} log(k log N/ε)).
The hidden constants may depend on c."

**Formalization Note.**
* "A randomized algorithm" is one admissible program `P` of `NonadaptiveSFT.Machine` (§2.3's exact
  arithmetic model with a `ℤ/2^aℤ` coordinate bank, fair coins and point queries), chosen before `c`:
  `c` is an input, as in Algorithm 1. The constant `C` depends on `c` only and is chosen before
  `a, d, ε, k, X, B`. `log = log₂` and `log N = a·d`.
* Input `NonadaptiveSFT.goalInit a d k ε B c` (integers `a, d, k`; reals `ε, B, c` and the supplied root
  of unity `cos(2π/2^a)`, `sin(2π/2^a)`). Output on halt: decoded list `0` is `X̃^pre`, decoded list `1`
  is `X̃`.
* On **every** coin tape: the run halts with `work ≤ C·k^{7/2}ε^{−7}(ad)^{9/4}log₂(k·ad/ε)`; a halted run
  has made at most `N = 2^{ad}` and at most `C·(k/ε²)·ad·log₂(k/ε)` queries; `|supp X̃^pre| ≤ C·k/ε²`
  and `X̃ = H_k(X̃^pre)`.
* Nonadaptivity ("all query locations are chosen in advance using randomness", p.2): on a fixed
  tape, the query log at halt is the same for every signal `X'` (same parameters `a, d, k, ε, B, c`).
* A measurable set of tapes of probability at least `9/10` on which both error bounds (3) hold.
* `H_k` breaks ties by the lexicographic order on `G` (`lexKey`); the page fixes an arbitrary order.
  `σ_k(X̂)₂ = ‖X̂ − H_k(X̂)‖₂`. `B = 0` (exactly `k`-sparse spectra) is included. -/
theorem theorem_1 :
    ∃ (P : Program) (_ : Admissible P), ∀ c : ℝ, 1 ≤ c → ∃ C : ℝ, 0 < C ∧
      ∀ (a d : ℕ), 1 ≤ a → 1 ≤ d → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      ∀ (k : ℕ), 2 ≤ k → k < 2 ^ (a * d) → ∀ (X : G a d → ℂ) (B : ℝ),
        sigma (lexKey a d) k (hat X) ≤ B → B ≤ c * sigma (lexKey a d) k (hat X) →
        let σ := sigma (lexKey a d) k (hat X)
        let L : ℝ := (a * d : ℕ)
        let s₀ := goalInit a d k ε B c
        (∀ ω : ℕ → Bool, ∃ n : ℕ, (run P X s₀ ω n).halted = true ∧
          ((run P X s₀ ω n).work : ℝ) ≤
            C * (k : ℝ) ^ (7 / 2 : ℝ) / ε ^ 7 * L ^ (9 / 4 : ℝ) * Real.logb 2 (k * L / ε)) ∧
        (∀ (ω : ℕ → Bool) (n : ℕ), (run P X s₀ ω n).halted = true →
          (run P X s₀ ω n).queries ≤ 2 ^ (a * d) ∧
          ((run P X s₀ ω n).queries : ℝ) ≤ C * (k / ε ^ 2) * L * Real.logb 2 (k / ε)) ∧
        (∀ (X' : G a d → ℂ) (ω : ℕ → Bool) (n n' : ℕ), (run P X s₀ ω n).halted = true →
          (run P X' s₀ ω n').halted = true →
          (run P X s₀ ω n).queryLog = (run P X' s₀ ω n').queryLog) ∧
        (∀ (ω : ℕ → Bool) (n : ℕ), (run P X s₀ ω n).halted = true →
          (suppCard (outVec (run P X s₀ ω n) 0) : ℝ) ≤ C * k / ε ^ 2 ∧
          outVec (run P X s₀ ω n) 1 = Hk (lexKey a d) k (outVec (run P X s₀ ω n) 0)) ∧
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ (9 / 10 : ENNReal) ≤ coinTape E ∧
          ∀ ω ∈ E, ∀ n : ℕ, (run P X s₀ ω n).halted = true →
            linf (hat X - outVec (run P X s₀ ω n) 0) ≤ ε / Real.sqrt k * σ ∧
            l2 (hat X - outVec (run P X s₀ ω n) 1) ^ 2 ≤ (1 + ε) * σ ^ 2 := by sorry

end NonadaptiveSFT
