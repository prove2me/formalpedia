-- Prove2me | Theorems.Thm_NonadaptiveSFT_Supplement_theorem_32
-- name    : NonadaptiveSFT.Supplement.theorem_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:03:24.106213+00:00
-- url     : https://prove2.me/theorems/b81df50b-d5e1-4aff-8eee-d7decfc5ea04
-- title:
--   Theorem 32 — constant-factor $\ell_2/\ell_2$ sparse Fourier recovery without a tail estimate, $O(k\log N\log k)$ nonadaptive queries
-- statement:
--   Let $a, d \ge 1$ be integers, $G = (\mathbb Z/2^a\mathbb Z)^d$, $N = 2^{ad}$, and $2 \le k < N$. For a signal $X : G \to \mathbb C$ write $\widehat X(f) = \frac1N\sum_{t\in G} X(t)\overline{\chi_f(t)}$ for its Fourier transform and $\sigma_k(\widehat X)_2 = \|\widehat X - H_k(\widehat X)\|_2$ for its best $k$-term approximation error in $\ell_2$, where $H_k$ keeps the $k$ largest-magnitude coordinates.
--
--   **Theorem (recovery without a tail estimate).** There are an absolute constant $C>0$ and a randomized algorithm, in the exact arithmetic model of §2.3, which is given only $a$, $d$, $k$ and point-query access to an arbitrary fixed $X \in \mathbb C^G$ (no signal norm and no tail estimate), such that on every execution
--
--   1. it halts after at most $C\,k^{7/2}(\log N)^{9/4}\log(k\log N)$ operations;
--   2. it makes at most $\min\{N,\ C\,k(\log N)\log k\}$ point queries, chosen nonadaptively (the query locations depend only on the random bits, never on $X$);
--   3. it returns a $k$-sparse vector $\widetilde X \in \mathbb C^G$;
--
--   and with probability at least $9/10$
--   $$
--   \|\widehat X - \widetilde X\|_2^2 \;\le\; C\,\sigma_k(\widehat X)_2^2 .
--   $$
--   In particular, if $\widehat X$ is $k$-sparse, then with probability at least $9/10$ the output equals $\widehat X$ exactly. All logarithms are base $2$.
--
--   This is the paper's constant-factor $\ell_2/\ell_2$ guarantee without side information: unlike Theorem 1, the algorithm needs no estimate $B$ of the tail $\sigma_k(\widehat X)_2$, and it handles an exactly sparse spectrum without being told so.
--
--   **Formalization Note** The algorithm is one admissible program of the published machine `NonadaptiveSFT.Machine`; its input state holds only the integers $a, d, k$ and the supplied root of unity $\cos(2\pi/2^a)$, $\sin(2\pi/2^a)$, and the output $\widetilde X$ is the decoded output list $0$. One constant $C$ serves the error bound and both resource bounds, and is chosen before $a, d, k, X$. Nonadaptivity is stated as: on a fixed coin tape the query log at halt is the same for every signal.
--
--   Differences from the source:
--
--   - encoding: a randomized algorithm in the computational model of Section 2.3 → one admissible program P of the published NonadaptiveSFT.Machine, chosen before every parameter; its coin tape is a fair-coin product measure and 'on every execution' means on every tape; reason: the base mission's published model and convention (§2.3, pp.18–19)
--   - encoding: input: point-query access to X, with no signal norm or tail estimate → integer memory a, d, k, the supplied root of unity cos(2π/2^a), sin(2π/2^a) in real memory, and the signal only as the query oracle; output X̃ is decoded list 0; reason: the base mission's published input/output layout convention; the root of unity is supplied by the §2.3 model
--   - encoding: nonadaptive point queries → on a fixed coin tape the query log at halt is the same for every signal X'; reason: the base mission's published formalization of nonadaptivity (p.2: query locations chosen in advance from the randomness)
--   - encoding: O(·) bounds with absolute hidden constants; log N → one constant C > 0 chosen after P and before a, d, k, X, multiplying each explicit bound; log = log₂ and log N = a·d; reason: 'All hidden constants are absolute' (one C can serve all bounds by taking the maximum); paper's convention log = log₂
--   - encoding: returns a k-sparse vector X̃ → on every tape, the output of a halted run has at most k nonzero coordinates; reason: the algorithm's return value is always k-sparse; the probabilistic clause is only the error bound
--   - encoding: σ_k(X̂)_2, the best k-sparse approximation error in ℓ_2 → sigma (lexKey a d) k (hat X) = ‖X̂ − H_k(X̂)‖₂ with the published tie order; reason: base convention; the value does not depend on the tie order
--   - encoding: in particular, if X̂ is k-sparse, the algorithm recovers it exactly with probability at least 9/10 → on the same probability-9/10 event, σ_k(X̂)₂ = 0 implies X̃ = X̂; reason: X̂ is k-sparse iff σ_k(X̂)₂ = 0; stated on the same event as the main bound, which is what the page derives it from
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Theorem 32, p.48 (PDF p.50); informal form Theorem 2, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Machine

namespace NonadaptiveSFT

namespace Supplement

/-- **Theorem 32** (Recovery without a tail estimate; detailed form of Theorem 2), p.48 (PDF p.50);
informal form Theorem 2, p.3 (PDF p.5).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

"Let a, d ≥ 1 be integers, G = (Z/2^aZ)^d, N = 2^{ad}, and 2 ≤ k < N. There are an absolute constant
C and a randomized algorithm which, given point-query access to any fixed X ∈ C^G, returns a k-sparse
vector X̃ ∈ C^G such that, with probability at least 9/10, ∥X̂ − X̃∥₂² ≤ C σ_k(X̂)₂². … No signal norm
or tail estimate is supplied. The algorithm makes at most min{N, O(k(log N) log k)} nonadaptive point
queries and uses at most O(k^{7/2}(log N)^{9/4} log(k log N)) exact operations on every execution, in
the computational model of Section 2.3. All hidden constants are absolute. In particular, if X̂ is
k-sparse, the algorithm recovers it exactly with probability at least 9/10."

**Formalization Note.**
* "A randomized algorithm" is one admissible program `P` of `NonadaptiveSFT.Machine` (§2.3's exact
  arithmetic model), the same for every `a, d, k, X`. One absolute constant `C > 0`, chosen after `P`
  and before `a, d, k, X`, serves the error bound and both `O(·)`s. `log = log₂`, `log N = a·d`.
* Input: integer memory `a, d, k`; real memory only the supplied root of unity `cos(2π/2^a)`,
  `sin(2π/2^a)` (`rootReals a`); coordinate memory empty. No signal norm, tail estimate or other
  signal-dependent number is supplied. Output on halt: decoded list `0` is `X̃`.
* On **every** coin tape: the run halts with `work ≤ C·k^{7/2}(ad)^{9/4}log₂(k·ad)`; a halted run has
  made at most `N = 2^{ad}` and at most `C·k·ad·log₂ k` queries, and its output has at most `k`
  nonzero coordinates.
* Nonadaptivity: on a fixed tape, the query log at halt is the same for every signal `X'`.
* A measurable set of tapes of probability at least `9/10` on which `‖X̂ − X̃‖₂² ≤ C σ_k(X̂)₂²`, and on
  which `X̃ = X̂` whenever `σ_k(X̂)₂ = 0` (the page's "in particular").
* `σ_k(X̂)₂ = ‖X̂ − H_k(X̂)‖₂` with the published lexicographic tie order (the value does not depend
  on it). -/
theorem theorem_32 :
    ∃ (P : Program) (_ : Admissible P) (C : ℝ), 0 < C ∧
      ∀ (a d : ℕ), 1 ≤ a → 1 ≤ d → ∀ (k : ℕ), 2 ≤ k → k < 2 ^ (a * d) →
      ∀ X : G a d → ℂ,
        let σ := sigma (lexKey a d) k (hat X)
        let L : ℝ := (a * d : ℕ)
        let s₀ : State a d := initState a d [(a : ℤ), (d : ℤ), (k : ℤ)] (rootReals a) []
        (∀ ω : ℕ → Bool, ∃ n : ℕ, (run P X s₀ ω n).halted = true ∧
          ((run P X s₀ ω n).work : ℝ) ≤
            C * (k : ℝ) ^ (7 / 2 : ℝ) * L ^ (9 / 4 : ℝ) * Real.logb 2 (k * L)) ∧
        (∀ (ω : ℕ → Bool) (n : ℕ), (run P X s₀ ω n).halted = true →
          (run P X s₀ ω n).queries ≤ 2 ^ (a * d) ∧
          ((run P X s₀ ω n).queries : ℝ) ≤ C * k * L * Real.logb 2 k) ∧
        (∀ (X' : G a d → ℂ) (ω : ℕ → Bool) (n n' : ℕ), (run P X s₀ ω n).halted = true →
          (run P X' s₀ ω n').halted = true →
          (run P X s₀ ω n).queryLog = (run P X' s₀ ω n').queryLog) ∧
        (∀ (ω : ℕ → Bool) (n : ℕ), (run P X s₀ ω n).halted = true →
          suppCard (outVec (run P X s₀ ω n) 0) ≤ k) ∧
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ (9 / 10 : ENNReal) ≤ coinTape E ∧
          ∀ ω ∈ E, ∀ n : ℕ, (run P X s₀ ω n).halted = true →
            l2 (hat X - outVec (run P X s₀ ω n) 0) ^ 2 ≤ C * σ ^ 2 ∧
            (σ = 0 → outVec (run P X s₀ ω n) 0 = hat X) := by sorry

end Supplement

end NonadaptiveSFT
