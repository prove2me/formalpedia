-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_Supplement_theorem_16
-- name    : IsingVectorBalancing.Subgaussian.Supplement.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:22:01.170603+00:00
-- url     : https://prove2.me/theorems/baf8340f-d835-440f-a105-47b0fe986bb8
-- title:
--   Theorem 16 — General complete-graph Lorentzian spin-system gap c_A/n, including the positive-diagonal consequence
-- statement:
--   Let $q\ge2$ and let $A$ be symmetric, entrywise nonnegative, have at most one positive eigenvalue and no zero row. For any positive-vector decomposition $A_{ab}=\rho_a\rho_b-\langle R_a,R_b\rangle$, with $\rho_a>0$, set
--
--   $$c_A=\min_a\frac{A_{aa}}{\rho_a^2}=\min_a\left(1-\|R_a/\rho_a\|_2^2\right).$$
--
--   If $c_A>0$, then for every $n\ge2$ and all nonnegative activities $\lambda_i(a)$ with $Z_A(\lambda)>0$, the complete-graph Gibbs law has random-scan heat-bath kernel $P$ satisfying
--
--   $$\operatorname{gap}(P)\ge c_A/n.$$
--
--   If every diagonal entry $A_{aa}$ is positive, a positive-vector decomposition exists with $c_A>0$, and the same bound holds uniformly over $n$ and all allowed activities. The decomposition and constant are chosen from $A$ before $n$ and the activities, making the $\Omega_A(1/n)$ consequence explicit. Zero activities, zero off-diagonal entries, singular or rank-one matrices and singleton support are retained. This companion theorem uses Lemmas 17–18 and is not used in the proof of the concentration goal.
--
--   Differences from the source:
--   - encoding: finite sets [n] and [q], real Euclidean vectors and finite expectations → Fin indices, EuclideanSpace, and finite sums; reason: the carriers and values are unchanged; Bool encodes the binary signs when present
--   - encoding: gap(P) bounded below on the feasible state space → the published finite Poincaré inequality with rates equal to the discrete transition matrix P; reason: its Laplacian is I−P on the support, so no time rescaling or irreducibility premise is introduced; singleton support is retained
--   - generalization: the Perron–Frobenius decomposition (23) → every positive-vector decomposition satisfying (23); reason: the proof uses only that identity and positivity of ρ, and therefore includes the source choice
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), p. 17 (PDF 18), Theorem 16, (21)–(24); proof pp. 20–21 (PDF 21–22)

import Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_Decomposition

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- Theorem 16, p.17/PDF18. The positive-diagonal consequence chooses one
constant from A before quantifying over n and the external activities. -/
theorem theorem_16 {q : ℕ} (hq : 2 ≤ q)
    (A : Matrix (Fin q) (Fin q) ℝ) (hA : ColorInteraction A) :
    (∀ (r : ℕ) (D : PositiveDecomposition A r), 0 < cA D →
      ∀ (n : ℕ), 2 ≤ n → ∀ activity : Fin n → Fin q → ℝ,
      (∀ i a, 0 ≤ activity i a) → 0 < colorPartition A activity →
      SubsetConvFPRAS.HasPoincare (colorLaw A activity) (MarkovMixing.glauber (colorLaw A activity))
        (cA D / (n : ℝ))) ∧
    ((∀ a, 0 < A a a) → ∃ (r : ℕ) (D : PositiveDecomposition A r), 0 < cA D ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ activity : Fin n → Fin q → ℝ,
      (∀ i a, 0 ≤ activity i a) → 0 < colorPartition A activity →
      SubsetConvFPRAS.HasPoincare (colorLaw A activity) (MarkovMixing.glauber (colorLaw A activity))
        (cA D / (n : ℝ))) := by sorry

end IsingVectorBalancing.Subgaussian.Supplement
