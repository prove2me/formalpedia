-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_theorem_3
-- name    : MatrixSenseRank.Testing.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:48:09.103197+00:00
-- url     : https://prove2.me/theorems/f52551b5-57ae-4956-9c91-7490b1ab674d
-- title:
--   Theorem 3 — dimension-independent noisy low-rank testing
-- statement:
--   There are absolute constants $a>0$ and an integer $d\ge1$ such that for every $k\ge1$, every $\varepsilon>0$, and every known Borel probability noise law $\eta$ with finite moments through order $4k+4$, there is a label-only finite-sample test using
--   $$T\le\left\lceil a\left(1+k!+m_{4k+4}(\eta)+\varepsilon^{-k}\right)^d\right\rceil.$$
--   The count and test are fixed before the dimensions and hidden target. For all dimensions $n,m$ (no relation to $k$ is imposed) and every unknown real $n\times m$ matrix $A$ with $\|A\|_F=1$, draw independent observations
--   $$X=gh^\top,\quad g\sim N(0,I_n),\quad h\sim N(0,I_m),\qquad y=\langle A,X\rangle+e,\quad e\sim\eta.$$
--   All draws are fresh, and noise is independent of measurements. LowRankTester discards $X$ and applies the same label test. It satisfies
--   $$\operatorname{rank}(A)\le k\ \Longrightarrow\ \Pr[\mathrm{accept}]\ge9/10,\qquad
--   \operatorname{dist}_k(A)\ge\varepsilon\ \Longrightarrow\ \Pr[\mathrm{reject}]\ge9/10.$$
--   No answer is prescribed between the promises. The distance is the infimum over unit-Frobenius matrices of rank at most $k$, not over unrestricted-norm approximants.
--
--   As specified in §6, the chosen label test also satisfies the full sparsity guarantee for the product-normal input law at norm parameter $C=1$ and accuracy $\varepsilon/2$. Its existence is part of the conclusion, not an assumed oracle. This establishes the full arbitrary-noise upper bound with no ambient-dimension dependence.
--
--   **Formalization Note** The source gives no numerical polynomial coefficient or degree. The fixed universal power-of-sum bound has exactly its uniform polynomial meaning. The identities $m_{4k+4}(GH)=((4k+3)!!)^2$, $\kappa_{2j}(GH)=(2j-1)!$ and $\tau=1$ are proof obligations, never assumptions. For instance, the elementary bounds $((4k+3)!!)^2\le11025(k!)^{72}$ and $2^k\le2k!$ for $k\ge1$ absorb that moment and the $\varepsilon/2$ change into fixed polynomial constants. All positive real accuracies remain quantified, including the regimes with no far matrices.
--
--   Differences from the source:
--   - encoding: poly(k!, m₄ₖ₊₄(η), (1/ε)^k) and finite even noise moments → positive absolute coefficient and fixed positive integer degree quantified before all parameters, with ceiling-rounded sample count and integrability through the same highest even order; reason: powers of one plus the nonnegative arguments express exactly a fixed absolute polynomial upper bound; no instance is excluded by stating the equivalent lower-moment integrability
--   - generalization: an algorithm LowRankTester taking samples (X, ⟨A,X⟩+η) → a label-only test (a Boolean kernel on the labels, composed with the projection discarding X) that additionally satisfies the full Theorem 14 sparsity guarantee for D=GH, C=1 and accuracy ε/2; reason: this is the §6 construction; restricting the existential to label-only tests and adding the sparsity-guarantee conjunct only strengthens the conclusion, and dropping both conjunct and restriction gives exactly the source's Theorem 3
--   - encoding: the noise distribution or needed moments are known to the algorithm → the test may depend on η but its universal sample bound uses only m₄ₖ₊₄(η); reason: §1.2 permits knowledge of the law; arbitrary noncentered and nonsymmetric continuous or discrete finite-moment laws are retained
--   - encoding: distₖ(A) is defined by Eq. (3) only for 1 ≤ k ≤ min(n₁,n₂) → all n, m are quantified; when k > min(n,m) the Lean infimum is 0 (A itself is feasible), so only the completeness clause has content there; reason: Theorem 3 places no relation between k and the dimensions; outside Eq. (3)'s domain the source's soundness clause is undefined and the Lean one is vacuous, while the completeness clause is the source's
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, STOC 2027 submission #380 (October 2026), Theorem 3, printed p. 4 / PDF p. 5, repeated §6, printed p. 26 / PDF p. 27, and full proof printed pp. 27–28 / PDF pp. 28–29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf; PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b.

import Mathlib
import Definitions.Def_MatrixSenseRank_Testing_Experiment

set_option autoImplicit false
open MeasureTheory

namespace MatrixSenseRank.Testing

/-- Theorem 3, printed p.4 / PDF p.5; §6, printed pp.26–28 / PDF pp.27–29.
Absolute polynomial constants precede every parameter; the label test is chosen before A.
The §6 construction uses the product-normal sparsity tester at C=1 and epsilon/2. -/
theorem theorem_3 :
    ∃ a : ℝ, 0 < a ∧ ∃ d : ℕ, 1 ≤ d ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (ε : ℝ), 0 < ε →
      ∀ (η : Measure ℝ), IsProbabilityMeasure η → FiniteMoments η (4 * k + 4) →
      ∃ (T : ℕ) (test : StatisticalTest ℝ T),
        T ≤ polynomialBound a d [(k.factorial : ℝ), rawMoment η (4 * k + 4),
          (1 / ε) ^ k] ∧
        SparsityGuarantee test productNormal η k (ε / 2) 1 ∧
        ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℝ), frobenius A = 1 →
          (A.rank ≤ k → (9 : ℝ) / 10 ≤ matrixAcceptance test η A) ∧
          (ε ≤ rankDistance k A → matrixAcceptance test η A ≤ (1 : ℝ) / 10) := by sorry

end MatrixSenseRank.Testing
