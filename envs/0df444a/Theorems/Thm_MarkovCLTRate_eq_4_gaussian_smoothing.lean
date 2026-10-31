-- Prove2me | Theorems.Thm_MarkovCLTRate_eq_4_gaussian_smoothing
-- name    : MarkovCLTRate.eq_4_gaussian_smoothing
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:19.232015+00:00
-- url     : https://prove2.me/theorems/ec9da0ca-f744-4ee1-ad51-4d499034d7cf
-- title:
--   (4): Gaussian-smoothing bounds and the Hölder bound on $\nabla^2 P_A h$
-- statement:
--   Fix the dimension $d$. There is a constant $C$ such that, for every positive definite covariance $A$ and every $h\in Lip_1$, the Gaussian convolution $P_Ah(x)=E[h(x+A^{1/2}Z)]$ is four times continuously differentiable and
--   $$
--   \|\nabla^jP_Ah\|_{op}\le C\|A^{-1/2}\|_{op}^{j-1},\qquad j=2,3,4,
--   $$
--   and, for every $\beta\in(0,1)$ and all $x,y$,
--   $$
--   \|\nabla^2P_Ah(x)-\nabla^2P_Ah(y)\|_{op}\le C\|A^{-1/2}\|_{op}^{1+\beta}\|x-y\|^\beta,\qquad(4)
--   $$
--   with $C$ uniform over $\beta\in(0,1)$.
--
--   These are the smoothing estimates behind the three-part comparison of $H_k$ and $H_{k-1}$ in Lemma 3 and in the proof of Theorem 3.
--
--   **Formalization Note** $\nabla^j$ is the $j$th Fréchet derivative with the multilinear operator norm (p.11). $C$ may depend on $d$ and is chosen before $A$, $h$, $\beta$, $x$, $y$.
--
--   Differences from the source:
--   - reading: the differentiation is justified by the standard Gaussian-smoothing bounds → ContDiff ℝ 4 (P_A h) as a conclusion; reason: the bounds presuppose that the derivatives exist; stating it rules out derivatives defaulting to 0
--   - reading: C (in Lemma 3, depending on d) → ∀ d, ∃ C, ∀ A h β x y; reason: the page makes C uniform over β; it depends on the dimension (Lemma 3 lists d among the dependencies)
--   - encoding: ‖A^{−1/2}‖_op → opNorm (CFC.sqrt A)⁻¹; reason: the inverse of the positive square root, on positive definite A
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Lemma 3, pp.11–12, Gaussian-smoothing bounds and (4)

import Mathlib
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_Stein

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **Gaussian smoothing bounds and (4)**, arXiv:2401.15719v5, proof of Lemma 3, pp.11–12. For
`h ∈ Lip_1` and a positive definite covariance `A`, the Gaussian convolution
`P_A h(x) = E[h(x + A^{1/2}Z)]` satisfies
`‖∇^j P_A h‖_op ≤ C ‖A^{−1/2}‖_op^{j−1}`, `j = 2, 3, 4`,
and, for every `β ∈ (0, 1)`,
`‖∇²P_A h(x) − ∇²P_A h(y)‖_op ≤ C ‖A^{−1/2}‖_op^{1+β} ‖x − y‖^β`   (4),
with `C` uniform over `β ∈ (0, 1)`.

**Formalization Note.** `C` depends only on the dimension `d`, and is quantified before `A`, `h`,
`β`, `x`, `y`. `∇^j` is the `j`-th Fréchet derivative (`iteratedFDeriv`) with the multilinear
operator norm (p.11); the statement also asserts that `P_A h` is four times continuously
differentiable, so these derivatives are genuine. -/
theorem eq_4_gaussian_smoothing (d : ℕ) :
    ∃ C : ℝ, ∀ (A : Mat d), A.PosDef → ∀ h : Vec d → ℝ, LipschitzWith 1 h →
      ContDiff ℝ 4 (gaussSmooth A h) ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ 4 → ∀ x : Vec d,
          ‖iteratedFDeriv ℝ j (gaussSmooth A h) x‖ ≤ C * opNorm (minvSqrt A) ^ (j - 1)) ∧
      (∀ β : ℝ, 0 < β → β < 1 → ∀ x y : Vec d,
          opNorm (hessMat (gaussSmooth A h) x - hessMat (gaussSmooth A h) y)
            ≤ C * opNorm (minvSqrt A) ^ (1 + β) * ‖x - y‖ ^ β) := by sorry

end MarkovCLTRate
