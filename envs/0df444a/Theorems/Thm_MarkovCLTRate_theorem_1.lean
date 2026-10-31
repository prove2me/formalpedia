-- Prove2me | Theorems.Thm_MarkovCLTRate_theorem_1
-- name    : MarkovCLTRate.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:11.105696+00:00
-- url     : https://prove2.me/theorems/9cc4d210-b9ef-4473-897c-277e1fed9fc4
-- title:
--   Theorem 1: Wasserstein bound for the multivariate martingale CLT
-- statement:
--   Let $\{m_k\}$ be a $d$-dimensional martingale difference sequence satisfying Assumption 1 for a fixed $\beta\in(0,1)$, fix $n\ge1$, and assume that
--   $$
--   V_k=\sum_{j=k}^nE(\Sigma_j)
--   $$
--   is positive definite for each $k=1,\dots,n$. With $D_k=V_k^{-1/2}E(\Sigma_k)V_k^{-1/2}$, $W_n=S_n/\sqrt n$ and $Z\sim N(0,I)$,
--   $$
--   d_{\mathcal W}\big(W_n,n^{-1/2}V_1^{1/2}Z\big)\le\frac1{\sqrt n}\sum_{k=1}^n\Big[\tilde C_1(d,\beta)\|V_k^{1/2}\|_{op}E\big(\|V_k^{-1/2}m_k\|^{2+\beta}\big)+\tilde C_1(d,\beta)\operatorname{Tr}(D_k)\|V_k^{1/2}\|_{op}E\big(\|V_k^{-1/2}m_k\|^{\beta}\big)\Big]+\Delta_n,
--   $$
--   where $\Delta_n$ is the covariance-interaction term. Moreover,
--   $$
--   \|A_{k,h}(\mathcal F_{k-1})\|_{op}\le C\|V_k^{1/2}\|_{op}\quad\text{a.s.},
--   $$
--   where $C$ is the constant in statement 3 of Lemma 1.
--
--   This nonasymptotic martingale CLT is the tool behind every Markov chain rate in the paper: the Markov chain enters only through the martingale increments of a Poisson-equation decomposition.
--
--   **Formalization Note** $n^{-1/2}V_1^{1/2}Z$ has law `multivariateGaussian 0 (n⁻¹ V_1)`. The constant $C$ is universal and is chosen first.
--
--   Differences from the source:
--   - generalization: ‖A_{k,h}(𝓕_{k−1})‖_op ≤ C‖V_k^{1/2}‖_op a.s. → ‖steinA h V_k^{1/2} Λ_k a‖ ≤ C‖V_k^{1/2}‖ for every shift a ∈ ℜ^d; reason: A_{k,h}(𝓕_{k−1}) is this deterministic function at a = S_{k−1}, so the bound for every a gives the almost-sure bound
--   - encoding: A_{k,h}(𝓕_{k−1}) = E[∇²f_{k,h}(Z̃_k) | 𝓕_{k−1}] on an extended probability space → steinA at the shift a = S_{k−1}, with Z̃_k ∼ N(0, Λ_k) integrated out; reason: Z̃_k is independent of 𝓕_{k−1} and f_{k,h} depends on S_{k−1} only; no extension of the probability space is needed
--   - encoding: n^{−1/2}V_1^{1/2}Z with Z ∼ N(0, I) → multivariateGaussian 0 (n⁻¹ • V_1); reason: the law of n^{−1/2}V_1^{1/2}Z; Mathlib builds that measure from the same square root
--   - encoding: C, the constant in statement (3) of Lemma 1 → one universal ∃ C before d, the probability space, m, β and n; reason: Lemma 1(3)'s constant is independent of d and β; any constant valid there is valid here
--   - encoding: d_W and ∆_n as real suprema over Lip_1 → dW and deltaN valued in ℝ≥0∞, the Taylor sum embedded by ENNReal.ofReal; reason: a real ⨆ over the unbounded family Lip_1 would be the junk value 0; on finite values the two agree
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, Theorem 1, p.6

import Mathlib
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_Stein
import Definitions.Def_MarkovCLTRate_MartingaleCLT

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **Theorem 1** of arXiv:2401.15719v5, p.6. Let `(m_k)` be a `d`-dimensional martingale
difference sequence satisfying Assumption 1 for a fixed `β ∈ (0, 1)`, let
`V_k = Σ_{j=k}^n E(Σ_j)` be positive definite for `k = 1, …, n`, `D_k = V_k^{−1/2} E(Σ_k) V_k^{−1/2}`,
`W_n = S_n/√n` and `Z ∼ N(0, I)`. Then
`d_W(W_n, n^{−1/2} V_1^{1/2} Z) ≤ (1/√n) Σ_{k=1}^n [C̃₁ ‖V_k^{1/2}‖ E‖V_k^{−1/2}m_k‖^{2+β}
  + C̃₁ Tr(D_k) ‖V_k^{1/2}‖ E‖V_k^{−1/2}m_k‖^β] + ∆_n`,
and `‖A_{k,h}(𝓕_{k−1})‖_op ≤ C ‖V_k^{1/2}‖_op` a.s., where `C` is the constant of Lemma 1 (3).

**Formalization Note.** `n^{−1/2} V_1^{1/2} Z` has law `multivariateGaussian 0 (n⁻¹ V_1)`. The
matrix `A_{k,h}(𝓕_{k−1})` is the deterministic function `steinA` at the shift `a = S_{k−1}`
(see `Akh`); its bound is stated for every shift `a`, which gives the almost-sure bound. The
constant `C` is universal (the constant of Lemma 1 (3), independent of `d` and `β`), so it is
quantified first. -/
theorem theorem_1 :
    ∃ C : ℝ, ∀ (d : ℕ) {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
      [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d) (β : ℝ),
      0 < β → β < 1 → Assumption1 μ ℱ m β → ∀ n : ℕ, 1 ≤ n →
      (∀ k ∈ Finset.Icc 1 n, (covSum μ ℱ m n k).PosDef) →
        dW (μ.map (fun ω => (Real.sqrt n)⁻¹ • partialSum m n ω))
            (multivariateGaussian 0 ((n : ℝ)⁻¹ • covSum μ ℱ m n 1))
          ≤ ENNReal.ofReal (taylorBound μ ℱ m n β) + deltaN μ ℱ m n ∧
        ∀ k ∈ Finset.Icc 1 n, ∀ h : Vec d → ℝ, LipschitzWith 1 h → ∀ a : Vec d,
          opNorm (steinA h (msqrt (covSum μ ℱ m n k)) (lambdaMat μ ℱ m n k) a)
            ≤ C * opNorm (msqrt (covSum μ ℱ m n k)) := by sorry

end MarkovCLTRate
