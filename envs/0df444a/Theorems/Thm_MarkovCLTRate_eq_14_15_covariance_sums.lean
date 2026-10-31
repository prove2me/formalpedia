-- Prove2me | Theorems.Thm_MarkovCLTRate_eq_14_15_covariance_sums
-- name    : MarkovCLTRate.eq_14_15_covariance_sums
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:50.716764+00:00
-- url     : https://prove2.me/theorems/2b017448-f678-49c2-98da-b9fef7049299
-- title:
--   (14)–(15): two-sided bounds on $V_k$ and the Gaussian-target comparison
-- statement:
--   In the setting of the proof of Theorem 3, let $V_k=\sum_{j=k}^nE(\Sigma_j)$ and $q_k=n-k+1$, and assume $\Sigma_\infty\succ0$. Then:
--
--   1. there are $n_0$, $c>0$ and $C$ such that for all $n\ge n_0$
--   $$
--   cq_kI\preceq V_k\preceq Cq_kI,\qquad k=1,\dots,n;\qquad(14)
--   $$
--   2. $\frac1nV_1=\Sigma_\infty+O(n^{-1})$; $\quad(15)$
--   3. $d_{\mathcal W}\big(n^{-1/2}V_1^{1/2}Z,\ \Sigma_\infty^{1/2}Z\big)=O(n^{-1})$, $Z\sim N(0,I)$.
--
--   (14) lets Theorem 1 be applied to $W_n$ for large $n$, and items 2–3 replace its Gaussian target by the stationary one.
--
--   **Formalization Note** $\preceq$ is the Loewner order. The $O(\cdot)$ bounds of items 2–3 are stated with one constant for all $n\ge1$; the Gaussian laws are `multivariateGaussian`.
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - generalization: p = 2 + β (item 1 of Theorem 3), repeated with p = 4 on p.22 (item 2) → one exponent 2 < p ≤ 4 in ProofSetting, with ‖g‖^p ≤ C_r𝒱 and ‖V_r‖ ≤ C(1 + 𝒱^{1/p}); reason: the same argument covers both; p = 2 + β and p = 4 are the two instances, so the statement specializes to the page's
--   - reading: (14) "for all sufficiently large n", followed by "Enlarging the constants, if necessary, covers the finitely many remaining values of n" → (14) for n ≥ n₀ only; reason: the enlargement cannot work for the lower bound: for n = 1, d = 2 and a deterministic X_0, V_1 = v(X_0) can be singular (a one-step increment taking two values has rank one); the statement before the slip says sufficiently large n, and that is what the proof uses
--   - encoding: O(n^{−1}) in (15) and in the target comparison → ∃ C, ∀ n ≥ 1, … ≤ C/n; reason: every term is finite for each n, so one constant covers every n ≥ 1
--   - encoding: d_W(X, Y) = sup_{h ∈ Lip_1} E[h(X) − h(Y)], a real number → dW valued in ℝ≥0∞ (⊤ unless both laws are finite with finite first moments); reason: a real ⨆ over the unbounded family Lip_1 would be the junk value 0; every law compared here is a probability measure with a finite first moment, so the value is the page’s
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, p.19, (14), (15) and the Gaussian-target comparison

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_MartingaleCLT
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **The covariance sums, (14), (15) and the Gaussian target**, arXiv:2401.15719v5, proof of
Theorem 3, p.19. In the setting of the proof, let `V_k = Σ_{j=k}^n E(Σ_j)` and `q_k = n − k + 1`.
If `Σ_∞ ≻ 0`, then:
1. for all sufficiently large `n`, `c q_k I ⪯ V_k ⪯ C q_k I` for `k = 1, …, n`   (14);
2. `(1/n) V_1 = Σ_∞ + O(n^{−1})`   (15);
3. `d_W(n^{−1/2} V_1^{1/2} Z, Σ_∞^{1/2} Z) = O(n^{−1})`.

**Formalization Note.** (14) is stated for `n ≥ n₀` with `0 < c`, as in the sentence "for all
sufficiently large `n`" (for small `n`, `V_1` can be singular, so the lower bound cannot be
extended to every `n`). The `O(·)` bounds of (15) and of the target comparison are stated with one
constant for all `n ≥ 1`. `n^{−1/2} V_1^{1/2} Z` has law `multivariateGaussian 0 (n⁻¹ V_1)`, and
`⪯` is the Loewner order (`PosSemidef` of the difference). -/
theorem eq_14_15_covariance_sums {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (r : S → Vec d) (p Cr : ℝ) (V : S → Vec d)
    (hset : ProofSetting P π η lyap lam L r p Cr V) (hSig : (sigmaInf P π V).PosDef) :
    (∃ (n₀ : ℕ) (c C : ℝ), 0 < c ∧ ∀ n : ℕ, n₀ ≤ n → ∀ k ∈ Finset.Icc 1 n,
      (covSum (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k
          - (c * ((n : ℝ) - k + 1)) • (1 : Mat d)).PosSemidef ∧
      Matrix.PosSemidef ((C * ((n : ℝ) - k + 1)) • (1 : Mat d)
          - covSum (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k)) ∧
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      opNorm ((n : ℝ)⁻¹ •
          covSum (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n 1
        - sigmaInf P π V) ≤ C / n) ∧
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      dW (multivariateGaussian 0 ((n : ℝ)⁻¹ •
            covSum (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n 1))
          (multivariateGaussian 0 (sigmaInf P π V))
        ≤ ENNReal.ofReal (C / n) := by sorry

end MarkovCLTRate
