-- Prove2me | Theorems.Thm_NonadaptiveSFT_Supplement_theorem_36
-- name    : NonadaptiveSFT.Supplement.theorem_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:03:53.459322+00:00
-- url     : https://prove2.me/theorems/66720fa2-8ef3-4532-a244-3bed3eb4f05f
-- title:
--   Theorem 36 — $(1+\varepsilon)\sigma_k^2+\delta\|\widehat X\|_2^2$ sparse Fourier recovery without a tail estimate
-- statement:
--   Let $a, d \ge 1$ be integers, $G = (\mathbb Z/2^a\mathbb Z)^d$, $N = 2^{ad}$, $2 \le k < N$, $0 < \varepsilon \le 1/2$ and $0 < \delta \le 1/4$. For a signal $X : G \to \mathbb C$ write $\widehat X(f) = \frac1N\sum_{t\in G} X(t)\overline{\chi_f(t)}$ for its Fourier transform, $\|\widehat X\|_2$ for its total spectral energy, and $\sigma_k(\widehat X)_2 = \|\widehat X - H_k(\widehat X)\|_2$ for its best $k$-term approximation error in $\ell_2$.
--
--   **Theorem (recovery with relative additive error).** There are an absolute constant $C>0$ and a randomized algorithm, in the exact arithmetic model of §2.3, which is given only $a, d, k, \varepsilon, \delta$ and point-query access to an arbitrary fixed $X \in \mathbb C^G$ (no signal norm and no tail estimate), such that on every execution
--
--   1. it halts after at most
--   $$
--   C\Big(\frac{k^{7/2}}{\varepsilon^7}(\log N)^{9/4}\log\frac{k\log N}{\varepsilon}\,\log\frac1{\varepsilon\delta} \;+\; \frac{k^2}{\varepsilon^2}(\log N)\log^2\frac1{\varepsilon\delta}\,\log\log\frac1{\varepsilon\delta}\Big)
--   $$
--   operations;
--   2. it makes at most $\min\big\{N,\ C\frac{k}{\varepsilon^2}\big((\log N)\log\frac k\varepsilon + \log\log\frac1{\varepsilon\delta}\big)\big\}$ point queries, chosen nonadaptively;
--   3. it returns a $k$-sparse vector $\widetilde X$;
--
--   and with probability at least $9/10$
--   $$
--   \|\widehat X - \widetilde X\|_2^2 \;\le\; (1+\varepsilon)\,\sigma_k(\widehat X)_2^2 + \delta\,\|\widehat X\|_2^2 . \tag{69}
--   $$
--   All logarithms are base $2$; under the stated ranges $\log\frac1{\varepsilon\delta} \ge 3$, so every logarithm in the bounds is positive.
--
--   This keeps the $(1+\varepsilon)$ approximation factor of Theorem 1 without a supplied tail estimate, at the price of an additive error relative to the total spectral energy; the additive term remains when the spectrum is exactly $k$-sparse.
--
--   **Formalization Note** The algorithm is one admissible program of the published machine `NonadaptiveSFT.Machine`; its input state holds only the integers $a, d, k$, the reals $\varepsilon, \delta$ and the supplied root of unity, and the output $\widetilde X$ is the decoded output list $0$. One constant $C$ serves both resource bounds and is chosen before all parameters. $\|\widehat X\|_2$ is the Euclidean norm of the normalized spectrum, so $\|X\|_2 = \sqrt N\,\|\widehat X\|_2$.
--
--   Differences from the source:
--
--   - encoding: a randomized algorithm in the computational model of Section 2.3 → one admissible program P of the published NonadaptiveSFT.Machine, chosen before every parameter; its coin tape is a fair-coin product measure and 'on every execution' means on every tape; reason: the base mission's published model and convention (§2.3, pp.18–19)
--   - encoding: input: point-query access to X, with no signal norm or tail estimate → integer memory a, d, k and real memory ε, δ, the supplied root of unity cos(2π/2^a), sin(2π/2^a) in real memory, and the signal only as the query oracle; output X̃ is decoded list 0; reason: the base mission's published input/output layout convention; the root of unity is supplied by the §2.3 model
--   - encoding: nonadaptive point queries → on a fixed coin tape the query log at halt is the same for every signal X'; reason: the base mission's published formalization of nonadaptivity (p.2: query locations chosen in advance from the randomness)
--   - encoding: O(·) bounds with absolute hidden constants; log N → one constant C > 0 chosen after P and before a, d, k, ε, δ, X, multiplying each explicit bound; log = log₂ and log N = a·d; reason: 'All hidden constants are absolute' (one C can serve all bounds by taking the maximum); paper's convention log = log₂
--   - encoding: returns a k-sparse vector X̃ → on every tape, the output of a halted run has at most k nonzero coordinates; reason: the algorithm's return value is always k-sparse; the probabilistic clause is only the error bound
--   - encoding: σ_k(X̂)_2, the best k-sparse approximation error in ℓ_2 → sigma (lexKey a d) k (hat X) = ‖X̂ − H_k(X̂)‖₂ with the published tie order; reason: base convention; the value does not depend on the tie order
--   - encoding: ∥X̂∥_2 in (69) → l2 (hat X), the Euclidean norm of the normalized spectrum (the page's E); reason: the page defines E = ∥X̂∥_2 with the normalization of (1); not ∥X∥_2 = √N E
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Theorem 36 and eq. (69), pp.54–55 (PDF pp.56–57); informal form Theorem 3, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Machine

namespace NonadaptiveSFT

namespace Supplement

/-- **Theorem 36** (Recovery with relative additive error; detailed form of Theorem 3), pp.54–55
(PDF pp.56–57); informal form Theorem 3, p.3 (PDF p.5).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

"Let a, d ≥ 1 be integers, G = (Z/2^aZ)^d, N = 2^{ad}, 2 ≤ k < N, 0 < ε ≤ 1/2, and 0 < δ ≤ 1/4.
There is a randomized algorithm which, given point-query access to any fixed X ∈ C^G, returns a
k-sparse vector X̃ such that, with probability at least 9/10, ∥X̂ − X̃∥₂² ≤ (1 + ε)σ_k(X̂)₂² + δ∥X̂∥₂².
(69) No signal norm or tail estimate is supplied. The algorithm makes at most
min{N, O((k/ε²)((log N) log(k/ε) + log log(1/(εδ))))} nonadaptive point queries and uses at most
O((k^{7/2}/ε^7)(log N)^{9/4} log((k log N)/ε) log(1/(εδ)) + (k²/ε²)(log N) log²(1/(εδ)) log log(1/(εδ)))
exact operations on every execution, in the model of Section 2.3. All hidden constants are absolute."

**Formalization Note.**
* "A randomized algorithm" is one admissible program `P` of `NonadaptiveSFT.Machine` (§2.3's exact
  arithmetic model), the same for every `a, d, k, ε, δ, X`. One absolute constant `C > 0`, chosen
  after `P` and before all parameters, serves both `O(·)`s. `log = log₂`, `log N = a·d`.
* Input: integer memory `a, d, k`; real memory `ε, δ, cos(2π/2^a), sin(2π/2^a)`; coordinate memory
  empty. No signal norm, tail estimate or other signal-dependent number is supplied. Output on halt:
  decoded list `0` is `X̃`.
* With `ε ≤ 1/2`, `δ ≤ 1/4` we have `log₂(1/(εδ)) ≥ 3`, so `log₂ log₂(1/(εδ)) > 0`, and
  `log₂(k/ε) ≥ 2`, `log₂(k·ad/ε) ≥ 2`: every logarithm in the bounds is positive.
* On **every** coin tape: the run halts with work at most
  `C·[(k^{7/2}/ε^7)(ad)^{9/4}log₂(k·ad/ε)log₂(1/(εδ)) + (k²/ε²)(ad)(log₂(1/(εδ)))²log₂log₂(1/(εδ))]`;
  a halted run has made at most `N = 2^{ad}` and at most
  `C·(k/ε²)(ad·log₂(k/ε) + log₂log₂(1/(εδ)))` queries, and its output has at most `k` nonzero
  coordinates.
* Nonadaptivity: on a fixed tape, the query log at halt is the same for every signal `X'`.
* A measurable set of tapes of probability at least `9/10` on which (69) holds, with
  `‖X̂‖₂ = l2 (hat X)` the ℓ2 norm of the normalized spectrum (the page's `E`, not `‖X‖₂ = √N·E`). -/
theorem theorem_36 :
    ∃ (P : Program) (_ : Admissible P) (C : ℝ), 0 < C ∧
      ∀ (a d : ℕ), 1 ≤ a → 1 ≤ d → ∀ (k : ℕ), 2 ≤ k → k < 2 ^ (a * d) →
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 → ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 4 →
      ∀ X : G a d → ℂ,
        let σ := sigma (lexKey a d) k (hat X)
        let L : ℝ := (a * d : ℕ)
        let ℓ := Real.logb 2 (1 / (ε * δ))
        let s₀ : State a d :=
          initState a d [(a : ℤ), (d : ℤ), (k : ℤ)] ([ε, δ] ++ rootReals a) []
        (∀ ω : ℕ → Bool, ∃ n : ℕ, (run P X s₀ ω n).halted = true ∧
          ((run P X s₀ ω n).work : ℝ) ≤
            C * ((k : ℝ) ^ (7 / 2 : ℝ) / ε ^ 7 * L ^ (9 / 4 : ℝ) * Real.logb 2 (k * L / ε) * ℓ +
              (k : ℝ) ^ 2 / ε ^ 2 * L * ℓ ^ 2 * Real.logb 2 ℓ)) ∧
        (∀ (ω : ℕ → Bool) (n : ℕ), (run P X s₀ ω n).halted = true →
          (run P X s₀ ω n).queries ≤ 2 ^ (a * d) ∧
          ((run P X s₀ ω n).queries : ℝ) ≤
            C * (k / ε ^ 2) * (L * Real.logb 2 (k / ε) + Real.logb 2 ℓ)) ∧
        (∀ (X' : G a d → ℂ) (ω : ℕ → Bool) (n n' : ℕ), (run P X s₀ ω n).halted = true →
          (run P X' s₀ ω n').halted = true →
          (run P X s₀ ω n).queryLog = (run P X' s₀ ω n').queryLog) ∧
        (∀ (ω : ℕ → Bool) (n : ℕ), (run P X s₀ ω n).halted = true →
          suppCard (outVec (run P X s₀ ω n) 0) ≤ k) ∧
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ (9 / 10 : ENNReal) ≤ coinTape E ∧
          ∀ ω ∈ E, ∀ n : ℕ, (run P X s₀ ω n).halted = true →
            l2 (hat X - outVec (run P X s₀ ω n) 0) ^ 2 ≤
              (1 + ε) * σ ^ 2 + δ * l2 (hat X) ^ 2 := by sorry

end Supplement

end NonadaptiveSFT
