-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_Supplement_theorem_2
-- name    : MatrixSenseRank.Testing.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:13:22.322958+00:00
-- url     : https://prove2.me/theorems/d8544905-6fcd-48b6-8a0f-2a9d87d3081a
-- title:
--   Theorem 2 — polynomial-time noisy full-Gaussian rank-one tester
-- statement:
--   There is one polynomial-time two-stage Candès–Plan testing procedure with absolute sample coefficient $C_s>0$ and dimension threshold $n_0$. For all positive rectangular dimensions with $n=\max(n_1,n_2)\ge n_0$, known $\sigma\ge0$, and every $\varepsilon>0$, it uses a fixed integer number $T$ of independent full-Gaussian observations satisfying
--
--   $$T\le C_s\left[n(1+\sigma^2/\varepsilon^2)+(1+\sigma^2/\varepsilon^2)^2\right].$$
--
--   For every unknown unit-Frobenius target $A$, the same procedure accepts with probability at least $2/3$ if $\operatorname{rank}(A)\le1$, and rejects with probability at least $2/3$ if $\operatorname{dist}_1(A)\ge\varepsilon$. These are full matrix/label observations with independent $N(0,\sigma^2)$ noise. The test, recovery program, truncation program, and operation-count polynomials are all fixed without knowing $A$.
--
--   The operational procedure uses independent training and validation batches, rounds both batch sizes upward, obtains a rank-at-most-one outer-product candidate by a finite numerical truncation, and compares its validation residual sum to $(\sigma^2+\rho^2/2)T_2$. The internal accuracy is $\rho=\varepsilon/\sqrt2$; it preserves the paper's normalized-distance guarantee. The theorem asserts the numerical truncation property and uniform polynomial halting as conclusions and explicitly bounds the work of their composition, including intermediate-output precision.
--
--   This is the full two-term sample upper bound complementary to Theorem 1, without a low-rank promise on the target in the soundness case.
--
--   Differences from the source:
--   - encoding: finite real Euclidean matrices with the paper's Frobenius norm → matrices indexed by Fin n and Fin m, with the published Frobenius and normalized-distance definitions; reason: a change of coordinates and indexing only; positive dimensions are retained
--   - encoding: possibly randomized algorithms observing full sample pairs → measurable Boolean probability kernels averaged under the actual independent sample law; reason: this represents all internal randomization without removing observed covariates
--   - encoding: absolute asymptotic constants and sufficiently large dimensions → existential constants and thresholds preceding every dimension, accuracy, sample count and test; reason: the constants are uniform; no numerical coefficient is invented
--   - reading: "Let A be an unknown matrix" with soundness measured by dist_1(A) → the target ranges over unit-Frobenius matrices; reason: dist_1 is defined in §1.2, Eq. (3), for targets normalized to ||A||_F = 1, and the p.26 normalization paragraph states the guarantee for such targets; for a non-unit target dist_1 compares A with unit approximants and the printed claim fails (a rank-two A of norm 10 with tiny second singular value has dist_1 ≥ 9 and must be rejected, yet with the stated sample count it is indistinguishable from its rank-one part, which must be accepted)
--   - reading: polynomial-time numerical convex optimization and rank-one SVD without an explicit machine model → finite rational real-RAM programs with square roots, private fair coins and uniform polynomial operation bounds including logarithmic magnitude and accuracy; reason: this fixes the continuous-input interpretation of polynomial time and charges all subroutine and validation work
--   - encoding: Algorithm 1 uses an unnormalized rank-one approximation at its internal accuracy → external normalized accuracy epsilon uses rho=epsilon/sqrt(2), delta=rho/8, recovery accuracy delta/2, truncation tolerance delta/2, and upward-rounded batch sizes; reason: the printed p.26 normalization bound supplies sqrt(2); finite tolerances give candidate error at most 3delta/2 less than rho/4, preserving every probability and asymptotic sample term
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; Theorem 2, printed p. 21–22, PDF p. 22–23 (1-based).

import Definitions.Def_MatrixSenseRank_Testing_Supplement_Computation

set_option autoImplicit false

namespace MatrixSenseRank.Testing.Supplement

/-- Theorem 2, printed pp.21--22 / PDF pp.22--23. One algorithm and all its absolute
constants are fixed before dimensions, known noise, accuracy, and hidden target. -/
theorem theorem_2 :
    ∃ C Csample : ℝ, 0 < C ∧ 0 < Csample ∧
      ∃ (n₀ : ℕ) (P Q : PNormReg.Program) (K d L e : ℕ),
        0 < L ∧
        PolynomialHalting P K d ∧ PolynomialHalting Q K d ∧
        (∀ n m : ℕ, 0 < n → 0 < m → ∀ tol : ℝ, 0 < tol →
          ∀ (M : Mat n m) (ω : ℕ → Bool),
            ApproxRankOne M (numericalTruncation Q K d tol M ω) tol) ∧
        ∀ n m : ℕ, 0 < n → 0 < m → n₀ ≤ max n m →
          ∀ σ ε : ℝ, 0 ≤ σ → 0 < ε →
            let T := trainingCount C n m σ (ε / Real.sqrt 2) +
              validationCount σ (ε / Real.sqrt 2)
            (T : ℝ) ≤ Csample * ((max n m : ℕ) * (1 + σ ^ 2 / ε ^ 2) +
              (1 + σ ^ 2 / ε ^ 2) ^ 2) ∧
            ∃ test : StatisticalTest (Observation n m) T,
              ImplementsCandesPlan P Q K d C σ ε test ∧
              (∀ (s : Fin T → Observation n m) (ω : ℕ → Bool),
                candesPlanWork P K d C σ ε s ω ≤
                  workBound L e [(n : ℤ), (m : ℤ), (T : ℤ)]
                    (recoveryInputs σ ε s)) ∧
              RankGuarantee test (fullObservationLaw σ) 1 ε ((2 : ℝ) / 3) := by sorry

end MatrixSenseRank.Testing.Supplement
