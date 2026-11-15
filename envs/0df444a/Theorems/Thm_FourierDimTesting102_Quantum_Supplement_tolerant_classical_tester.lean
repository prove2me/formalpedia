-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_tolerant_classical_tester
-- name    : FourierDimTesting102.Quantum.Supplement.tolerant_classical_tester
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:35:33.498284+00:00
-- url     : https://prove2.me/theorems/934034b4-9c0b-424b-bcc9-b64450a31116
-- title:
--   Theorem 6.2 — Algorithm 4 tests tolerantly with $O(\frac{2^{k/2}k^2}{\epsilon(1-2\alpha)^2}\log\frac1{\epsilon(1-2\alpha)})$ classical queries
-- statement:
--   Fix $0<\epsilon<1$ and $0\le\alpha<1/2$. Algorithm 4 (with the parameters fixed in the Algorithms definition) makes at most
--
--   $$
--   C\,\frac{2^{k/2}(k+1)^2}{\epsilon(1-2\alpha)^2}\,\log\frac{1}{\epsilon(1-2\alpha)}
--   $$
--
--   classical queries to $f:\mathbb F_2^n\to\{-1,1\}$, for an absolute constant $C$ independent of $n,k,\alpha,\epsilon$ (for $k\ge1$ at most $4C\frac{2^{k/2}k^2}{\epsilon(1-2\alpha)^2}\log\frac1{\epsilon(1-2\alpha)}$), and for every $f$:
--
--   1. if $\operatorname{dist}(f,D_k)\le\alpha\epsilon$, Algorithm 4 accepts with probability at least $2/3$;
--   2. if $\operatorname{dist}(f,D_k)\ge\epsilon$, Algorithm 4 rejects with probability at least $2/3$.
--
--   This is the classical tolerant counterpart of Theorem 5.1, with the $2^{k/2}$ cost of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: boolean functions f : F₂ⁿ → {−1,1} → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x} (the base Model); reason: a bijection on the same functions; the bit is what the oracle returns
--   - encoding: classical query access: query x, obtain f(x) (§2.2) → a NonadaptiveRandAlg: a uniform seed fixes all query points, the output is computed from the seed and the answers; the query count is the number of query indices; reason: the algorithm in question is nonadaptive; repeated points are counted, so the count is the source’s worst-case count
--   - reading: Algorithm 4 with r = O(k log(1/(ϵ(1−2α)))), ℓ = O(2^{k/2}), T = O(kr/(ϵ(1−2α)²)), “adjusting the constant inside” → alg4 with r = k + 1 + ⌈log₂(1000·C(M,k+1))⌉, M = ⌈4096((k+1) ln(e/b) + ln 1000)/b²⌉, b = min(ε(1−2α), 1/2), ℓ as in Algorithm 2, T = ⌈max(1600, 32(kr ln 2 + ln 100))/(pε(1−2α)²)⌉; τ and p as printed; reason: the source leaves these constants open; r makes each of the three compression events of Theorem 6.1 fail with probability at most 1/1000, and T makes the Chebyshev and union-bound errors at most 1/100
--   - reading: Algorithm 4 for every 0 < ϵ < 1 → for ε > 1/2 the algorithm runs no rounds and accepts with zero queries; reason: no function is at distance above 1/2 from both constants, so there is no no-instance; the full range 0 < ε < 1 of the theorem is kept
--   - encoding: an arbitrary basis {w₁, …, w_k} of each W (line 2) → the basis Module.finBasisOfFinrankEq; reason: Φ_W(a) = Φ_W(a′) iff a + a′ ∈ W^⊥ for every basis, so C_W, the chosen pair, Z_W and the output do not depend on the basis
--   - reading: “use an unbiased rule to pick one (e.g., the lexicographically first such pair)” (line 9) → firstCollision, the lexicographically first pair i < j; reason: the source leaves “unbiased” undefined and names this rule as its example; it depends only on the labels Φ_W(a_i), which is what the proof of Lemma 6.3 uses
--   - generalization: O(2^{k/2}k²/(ϵ(1−2α)²) log(1/(ϵ(1−2α)))) for fixed ϵ, α (0 at k = 0) → C(k+1)²2^{k/2}/(ε(1−2α)²) · log(1/(ε(1−2α))) for every k ≥ 0, one absolute C; reason: for k ≥ 1, (k+1)² ≤ 4k² gives the source’s bound; the bound also covers k = 0 and is uniform in α and ε
--   - reading: at most distance αϵ from / ϵ-far from having Fourier dimension at most k → distToSet f (Dk n k) ≤ α·ε / ≥ ε; reason: Definition 2.6, with distance to D_k the minimum over its members
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.30, Theorem 6.2 (Algorithm 4, p.31; proof pp.32–33 with Lemmas 5.1, 6.3 and Theorem 6.1)

import Definitions.Def_FourierDimTesting102_Quantum_Supplement_Algorithms

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-- Theorem 6.2, p.30: there is an absolute constant `C` such that for all `n`, `k`, and all
`0 < ε < 1`, `0 ≤ α < 1/2`, Algorithm 4 (`alg4 n k α ε`, fixed before `f`) makes at most
`C (k+1)² 2^{k/2}/(ε(1−2α)²) · log(1/(ε(1−2α)))` classical queries, accepts (`true`) every `f` with
`dist(f, D_k) ≤ αε` with probability at least `2/3`, and rejects (`false`) every `f` with
`dist(f, D_k) ≥ ε` with probability at least `2/3`. -/
theorem tolerant_classical_tester :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (α ε : ℝ), 0 ≤ α → α < 1 / 2 → 0 < ε → ε < 1 →
      ((alg4 n k α ε).queries : ℝ) ≤ C * ((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ ((k : ℝ) / 2) /
          (ε * (1 - 2 * α) ^ 2) * Real.log (1 / (ε * (1 - 2 * α))) ∧
      ∀ f : BoolFn n,
        (distToSet f (Dk n k) ≤ α * ε → 2 / 3 ≤ (alg4 n k α ε).outProb f true) ∧
        (ε ≤ distToSet f (Dk n k) → 2 / 3 ≤ (alg4 n k α ε).outProb f false) := by sorry

end FourierDimTesting102.Quantum.Supplement
