-- Prove2me | Theorems.Thm_L22EigEst_Supplement_theorem_8
-- name    : L22EigEst.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:37:19.876203+00:00
-- url     : https://prove2.me/theorems/9ac834c1-17b7-43ea-a4f3-f0c56fd81558
-- title:
--   Theorem 8 — sample lower bound: $\Omega(\log(1/\varepsilon)/\varepsilon^2)$ rows or columns
-- statement:
--   **Theorem 8 (Sample Lower Bound).** There is an absolute constant $c>0$ with the following property. Let $\varepsilon\in(0,1/8)$, let $k=2\lfloor 1/(32\varepsilon^2)\rfloor$ (so $k\ge4$), let $m\ge k\ln k$ be an integer and $n=km$ (Definition 5.1). Then there is a probability distribution $\mathcal D$ over symmetric $n\times n$ real matrices such that the following holds for every $t\in\mathbb N$ and every randomized adaptive algorithm that receives the squared row norms $\|A_1\|_2^2,\dots,\|A_n\|_2^2$ and queries entries of $A$:
--
--   1. if, on every symmetric input and for every choice of its random bits, the algorithm queries at most $t$ distinct rows/columns, and
--   2. if, for $A\sim\mathcal D$, its output satisfies $|\hat\lambda_j-\lambda_j(A)|\le\varepsilon\|A\|_F$ for all $j\in[n]$ with probability at least $2/3$,
--
--   then
--
--   $$t\;\ge\; c\,\frac{\log(1/\varepsilon)}{\varepsilon^2}.$$
--
--   Here $\lambda_1(A)\ge\dots\ge\lambda_n(A)$ are the eigenvalues of $A$, and the probability is over both $A\sim\mathcal D$ and the algorithm's randomness.
--
--   The theorem shows that the principal submatrix of size $O(\log(1/\varepsilon)/\varepsilon^2)$ sampled by the paper's algorithm (Theorem 4) is optimal up to constants, even for adaptive algorithms that know the row norms.
--
--   **Formalization Note** Algorithms are `RandSpecAlg` (a `PMF` over adaptive query trees chosen from the row-norm list); `touched T A` is the set of indices appearing in the queries of $T$ on $A$; `successProb` is the joint success probability. The distribution $\mathcal D$ is existential, as printed.
--
--   Differences from the source:
--   - generalization: Definition 5.4: the algorithm outputs sorted estimates λ̂1 ≥ ⋯ ≥ λ̂n → the output λ̂ : Fin n → ℝ need not be sorted; reason: this enlarges the class of algorithms the lower bound covers; algorithms with sorted output are a special case, so the statement specializes to the source's
--   - reading: Ω(log(1/ε)/ε^a) as ε → 0 → one absolute constant c > 0, chosen before ε, m, D and the algorithm, with c·log(1/ε)/ε^a ≤ t for every ε ∈ (0, 1/8); reason: the Ω carries no threshold in the source and the theorem is stated for every ε ∈ (0, 1/8); the proof's explicit bound (k ln k/6 on p.30, k² ln k/96 on p.34, k = 2⌊1/(32ε²)⌋ ≥ 4) gives a uniform c over the whole range
--   - reading: Definition 5.1: m ≥ k log k → (k : ℝ) · Real.log k ≤ m (natural logarithm); reason: the base of log is unspecified; the natural logarithm is the weaker hypothesis on n, hence the stronger theorem, and the proofs use ln k (pp.30, 34)
--   - encoding: any (randomized, adaptive) algorithm which receives the squared row norms and, in the worst case, queries at most t distinct rows or columns → a PMF over adaptive probe trees (questions (j, j′), replies A_jj′, leaves the estimates), chosen from the row-norm list only; the budget holds for every symmetric input A and every tree in the support of alg (rowSq A); reason: p.27: 'on every input and every choice of its random bits'; Definition 5.4 fixes the query model; random bits are discrete
--   - encoding: success with probability at least 2/3 for A ∼ D → ∑_A D(A)·Pr_T[T succeeds on A] ≥ 2/3, success meaning A is symmetric and |λ̂_j − λ_j(A)| ≤ ε‖A‖_F for all j (λ sorted, 0-based); reason: the probability is over the input and the algorithm's coins jointly; D is supported on symmetric matrices, so the symmetry clause of success is automatic on D
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Theorem 8, p.26 (Definition 5.1, p.26; Definition 5.4 and the randomized-to-deterministic reduction, p.27; proof §5.1, pp.29–30)

import Definitions.Def_L22EigEst_Supplement_SpecQueryAlg

namespace L22EigEst.Supplement

/-- **Theorem 8 (Sample Lower Bound)** (p.26), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling
Algorithms for Eigenvalue Estimation*, STOC 2027 submission (manuscript sha256 b1f6adce…): "Given
ε ∈ (0, 1/8) and n as in Definition 5.1, there exists a distribution D over n × n symmetric matrices
such that any algorithm outputting an additive ε∥A∥F-approximation to the spectrum of A ∼ D with
probability at least 2/3 must, in the worst case, query Ω(log(1/ε)/ε²) rows or columns of A."

**Formalization Note.**
* `n` as in Definition 5.1 (p.26): `k = 2⌊1/(32ε²)⌋`, `m ≥ k log k` an integer (natural log), `n = km`.
* The Ω is one absolute constant `c > 0`, chosen before `ε`, `m`, `D` and the algorithm.
* "Any algorithm" is randomized and adaptive (`RandSpecAlg`): a `PMF` over adaptive query trees,
  chosen from the squared row norms only. "In the worst case" (p.27): the budget `t` on the number of
  distinct rows/columns queried holds on every symmetric input and every tree in the support.
* The success probability is over `A ∼ D` and the algorithm's randomness jointly (`successProb`).
* `D` is existential, as printed; the proof's witness is Definition 5.1's distribution. -/
theorem theorem_8 :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∀ k m n : ℕ, k = 2 * ⌊1 / (32 * ε ^ 2)⌋₊ → (k : ℝ) * Real.log k ≤ m → n = k * m →
      ∃ D : PMF (Matrix (Fin n) (Fin n) ℝ), (∀ A ∈ D.support, A.IsHermitian) ∧
        ∀ (t : ℕ) (alg : RandSpecAlg n),
          (∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian →
            ∀ T ∈ (alg (fun i => L22EigEst.rowSq A i)).support, (touched T A).card ≤ t) →
          (2 / 3 : ENNReal) ≤ successProb ε D alg →
          c * Real.log (1 / ε) / ε ^ 2 ≤ t := by sorry

end L22EigEst.Supplement
