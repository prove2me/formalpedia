-- Prove2me | Theorems.Thm_JointMixND_QuadOT_Supplement_theorem_2
-- name    : JointMixND.QuadOT.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:12:00.952961+00:00
-- url     : https://prove2.me/theorems/09295e06-4a60-41ce-868c-b6f3a13e36f3
-- title:
--   Theorem 2, pp. 7–8 — Gaussian marginals support an NCD, or an NA, joint mix iff 2 max σ_i² ≤ Σ σ_i²; such a joint mix can be chosen Gaussian
-- statement:
--   Let $F_i=N(m_i,\sigma_i^2)$, $i\in[n]$, be univariate Gaussian distributions with arbitrary means $m_i\in\mathbb R$ and variances $\sigma_i^2\ge0$ ($\sigma_i^2=0$ is the point mass at $m_i$). Then:
--
--   1. $(F_1,\dots,F_n)$ supports an NCD joint mix if and only if
--   $$2\max_{i\in[n]}\sigma_i^2\le\sum_{i\in[n]}\sigma_i^2;\tag{4}$$
--   2. $(F_1,\dots,F_n)$ supports an NA joint mix if and only if (4) holds;
--   3. if (4) holds, there is a multivariate Gaussian random vector with marginals $F_1,\dots,F_n$ that is a joint mix, NCD and NA.
--
--   Theorem 2 shows that (4) is necessary and sufficient for a negatively dependent joint mix with Gaussian marginals, which fails for general marginals.
--
--   **Formalization Note** $N(m,\sigma^2)$ is Mathlib's `gaussianReal m v` with `v : ℝ≥0`; "Gaussian random vector" is `IsGaussian` for the law on $\mathbb R^n$. Condition (4) is written as $2\sigma_j^2\le\sum_i\sigma_i^2$ for every $j$.
--
--   Differences from the source:
--   - encoding: a random vector X = (X_1, …, X_n) with components indexed by [n] → its law P on Fin n → ℝ, coordinates 0-based; reason: every notion involved depends on X only through its law; same instances
--   - encoding: 2 max_{i∈[n]} σ_i² ≤ Σ_{i∈[n]} σ_i² → ∀ j, 2 σ_j² ≤ Σ_i σ_i²; reason: equivalent for n ≥ 1; needs no special case at n = 0
--   - reading: supports an NCD or NA joint mix if and only if (4) → two equivalences, one for NCD and one for NA; reason: the printed 'NCD or NA' states the characterization for each notion, as the proof on pp. 23–25 does
--   - reading: such an NCD or NA joint mix can be chosen as a Gaussian random vector → under (4), a single Gaussian law with the given marginals that is a joint mix, NCD and NA; reason: the proof on p. 25 constructs one Gaussian vector; for Gaussian laws NCD and NA coincide (Proposition 1(a))
--   - reading: univariate Gaussian distributions with variances σ_i² → gaussianReal m_i v_i with v_i ≥ 0, point masses included; reason: the proof on p. 23 treats vanishing variances as the trivial case, so degenerate Gaussians are in scope
--   - generalization: vectors of positive dimension n → n : ℕ, including n = 0; reason: at n = 0 the unique probability law on the empty vector is Gaussian, a joint mix, NCD and NA, and the variance inequalities are vacuous; all positive-dimensional source instances are retained
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, pp. 7–8, Theorem 2 (proof pp. 23–25)

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic
import Definitions.Def_JointMixND_QuadOT_Supplement_Dependence

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace JointMixND.QuadOT.Supplement

theorem theorem_2 {n : ℕ} (m : Fin n → ℝ) (v : Fin n → ℝ≥0) :
    ((∃ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P ∧
        IsJointMix P ∧ IsNCD P) ↔ ∀ j, 2 * (v j : ℝ) ≤ ∑ i, (v i : ℝ)) ∧
    ((∃ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P ∧
        IsJointMix P ∧ IsNA P) ↔ ∀ j, 2 * (v j : ℝ) ≤ ∑ i, (v i : ℝ)) ∧
    ((∀ j, 2 * (v j : ℝ) ≤ ∑ i, (v i : ℝ)) →
      ∃ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P ∧
        IsJointMix P ∧ IsGaussian P ∧ IsNCD P ∧ IsNA P) := by sorry

end JointMixND.QuadOT.Supplement
