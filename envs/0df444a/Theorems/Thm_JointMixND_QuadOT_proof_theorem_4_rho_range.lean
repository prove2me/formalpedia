-- Prove2me | Theorems.Thm_JointMixND_QuadOT_proof_theorem_4_rho_range
-- name    : JointMixND.QuadOT.proof_theorem_4_rho_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:44.142511+00:00
-- url     : https://prove2.me/theorems/d9d241de-e25d-4f30-92f6-86bfd651cceb
-- title:
--   Proof of Theorem 4, p. 27 — an equicorrelation ρ with identical marginals lies in [−1/(n−1), 1]; ρ = −1/(n−1) is attained
-- statement:
--   Let $n\ge 2$ and let $F$ be a distribution on $\mathbb R$ with finite, positive variance $\sigma^2=\operatorname{Var}(F)$.
--
--   1. If $\mathbf X_\rho$ is a random vector with identical marginals $F$ whose correlation matrix has all off-diagonal entries equal to $\rho$, that is $\operatorname{Cov}(X_i,X_j)=\rho\,\sigma^2$ for $i\neq j$, then
--   $$-\frac1{n-1}\le\rho\le 1.$$
--   2. If moreover $F$ is $n$-completely mixable, the value $\rho=-1/(n-1)$ is attainable: there is a random vector with marginals $F$ and correlation matrix $P^*_n$.
--
--   Together with the symmetrization step, this lets the proof of Theorem 4 restrict attention to the one-parameter family $\mathbf X_\rho$, $\rho\in[-1/(n-1),1]$.
--
--   **Formalization Note** The proof normalizes $\operatorname{Var}(F)=1$ "without loss of generality"; the statement here keeps a general variance and assumes it positive, which is what makes a correlation defined. Correlations are written through covariances ($\operatorname{Cov}=\rho\sigma^2$). The bound $n\ge 2$ excludes the case without off-diagonal entries.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 27, Proof of Theorem 4 (second claim)

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Problems

namespace JointMixND.QuadOT

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 4, p. 27, second claim. (a) If `X_ρ` has identical marginals `F`
(finite, positive variance) and all off-diagonal correlations equal to `ρ`, then
`ρ ∈ [-1/(n-1), 1]`. (b) If `F` is `n`-completely mixable, the value `ρ = -1/(n-1)` is attained:
some random vector with marginals `F` has correlation matrix `P*_n`. -/
theorem proof_theorem_4_rho_range {n : ℕ} (hn : 2 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF2 : MemLp id 2 F) (hvar : 0 < variance id F) :
    (∀ (P : Measure (Fin n → ℝ)) (ρ : ℝ), IsCoupling F P →
        (∀ i j : Fin n, i ≠ j →
          covariance (fun x => x i) (fun x => x j) P = ρ * variance id F) →
        -1 / ((n : ℝ) - 1) ≤ ρ ∧ ρ ≤ 1) ∧
    (CompletelyMixable n F → ∃ P : Measure (Fin n → ℝ), IsCoupling F P ∧ HasCorrPstar F P) := by sorry

end JointMixND.QuadOT
