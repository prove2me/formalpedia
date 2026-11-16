-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_Supplement_proposition_12
-- name    : MatrixSenseRank.Testing.Supplement.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:12:31.442206+00:00
-- url     : https://prove2.me/theorems/e21ab08f-067e-484c-b096-395c25b49d1d
-- title:
--   Proposition 12 — polynomial-time Candès–Plan recovery
-- statement:
--   There are absolute constants $C,c,C'>0$ and one polynomial-time real-arithmetic program with this property. Let $A\in\mathbb R^{n_1\times n_2}$ have rank at most one, with arbitrary norm, let $n=\max(n_1,n_2)$, and let known $\sigma\ge0$ and requested error $\delta>0$ be given. From any integer number of independent full-Gaussian observations satisfying
--
--   $$T\ge Cn\max\{1,\sigma^2/\delta^2\},$$
--
--   the program returns $\widehat A$ with
--
--   $$\Pr\!\left[\|A-\widehat A\|_F\le\delta\right]\ge1-C'e^{-cn}.$$
--
--   The probability includes both the measurement and noise draws and private randomization. The program and its polynomial operation bound are existential conclusions, uniform over all dimensions, target magnitudes, noise scales and requested accuracies. No recovery promise is assumed of an input routine.
--
--   This supplies recovery of the rank-one class for the first stage of Algorithm 1. The zero target and noiseless case are included.
--
--   **Formalization Note** Polynomial time uses the explicit finite real-RAM program and precision/magnitude convention in the computational definition. The recovery map is asserted to be jointly measurable in the observations and the coin tape, so that the success event is an event.
--
--   Differences from the source:
--   - encoding: finite real Euclidean matrices with the paper's Frobenius norm → matrices indexed by Fin n and Fin m, with the published Frobenius and normalized-distance definitions; reason: a change of coordinates and indexing only; positive dimensions are retained
--   - reading: a polynomial-time convex-optimization algorithm on continuous Gaussian data, without a machine model → a finite rational real-RAM program with square roots and fair coins, uniform polynomial instruction count in dimensions, data length and logarithmic magnitude/accuracy; reason: this fixes the source's continuous-input arithmetic convention; exact-real Turing bit complexity is not asserted
--   - encoding: the probability of the recovery event over measurements, noise and the algorithm's randomness → an additional conclusion that the program's output is jointly measurable in the observations and the coin tape; reason: makes the success set an event so its probability is the ordinary measure; a finite real-RAM run is measurable, so no instance is excluded
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; Proposition 12, printed p. 22, PDF p. 23 (1-based).

import Definitions.Def_MatrixSenseRank_Testing_Supplement_Computation

set_option autoImplicit false
open MeasureTheory

namespace MatrixSenseRank.Testing.Supplement

/-- Proposition 12, printed p.22 / PDF p.23. Program syntax, halting and the recovery
probability are conclusions, never hypotheses. The target has arbitrary norm. -/
theorem proposition_12 :
    ∃ C c C' : ℝ, 0 < C ∧ 0 < c ∧ 0 < C' ∧
      ∃ (P : PNormReg.Program) (K d : ℕ), PolynomialHalting P K d ∧
        ∀ n m T : ℕ, 0 < n → 0 < m →
          ∀ σ δ : ℝ, 0 ≤ σ → 0 < δ →
            C * max n m * max 1 (σ ^ 2 / δ ^ 2) ≤ (T : ℝ) →
              Measurable (fun p : (Fin T → Observation n m) × (ℕ → Bool) =>
                recover P K d σ δ p.1 p.2) ∧
              ∀ A : Mat n m, A.rank ≤ 1 →
                1 - C' * Real.exp (-c * max n m) ≤
                  ((Measure.pi (fun _ : Fin T => fullObservationLaw σ A)).prod
                    PNormReg.coinTape).real
                      {p | frobenius (A - recover P K d σ δ p.1 p.2) ≤ δ} := by sorry

end MatrixSenseRank.Testing.Supplement
