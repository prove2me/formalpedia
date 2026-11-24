-- Prove2me | Theorems.Thm_KSPolySign_theorem_6_8_a
-- name    : KSPolySign.theorem_6_8_a
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T14:19:54.084978+00:00
-- url     : https://prove2.me/theorems/3500e1af-36da-42a3-92c4-0c340bcd8dfa
-- title:
--   Theorem 6.8(a): signs with $\|\sum_i\sigma_iA_i\|\le 3.4814\|\sum_iA_i^2\|^{1/2}$
-- statement:
--   This is part (a) of the main result (Theorem 6.8) of Song–Yue: the existence half of the rank-one matrix discrepancy bound.
--
--   Let $A_1,\dots,A_m\in\mathbb C^{n\times n}$ be Hermitian matrices, each of rank at most one. Then there are signs $\sigma\in\{-1,1\}^m$ such that
--
--   $$\Big\|\sum_{i=1}^m\sigma_iA_i\Big\|\;\le\;3.4814\,\Big\|\sum_{i=1}^mA_i^2\Big\|^{1/2},$$
--
--   where $\|\cdot\|$ is the operator norm induced by the Euclidean norm on $\mathbb C^n$.
--
--   The constant is $2\sqrt{\iota}$ with $\iota=3.03$ rounded up ($2\sqrt{3.03}\approx3.48138$). In the paper it follows from the semidefinite potential argument: a minimizer of the matrix potential on the cube $[-1,1]^m$ with the fewest active coordinates is a vertex, by endpoint moves (Lemma 3.10) and strict descent at light states (Lemma 2.7).
--
--   **Formalization Note** The statement is verbatim part (a) of `KSPolySign.theorem_6_8`; the operator norm is `AgnosticTNS.opNorm`, signs are the reals $\pm1$, and $\|X\|^{1/2}$ is `Real.sqrt`.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Theorem 6.8(a), p.68 (PDF p.68); Theorem 1.1, p.3

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_realOps
import Definitions.Def_KSPolySign_IsRatC
import Definitions.Def_KSPolySign_layout
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Theorem 6.8(a) (existence of signs).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Theorem 6.8(a), p.68 (PDF p.68); Theorem 1.1, p.3.
For Hermitian `A_1, …, A_m ∈ ℂ^{n×n}` of rank at most one there are signs `σ ∈ {±1}^m` with
`‖∑ σ_iA_i‖ ≤ 3.4814‖∑ A_i²‖^{1/2}`.
**Formalization Note** Verbatim part (a) of `KSPolySign.theorem_6_8`. -/
theorem theorem_6_8_a :
    (∀ (m n : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ i, (A i).IsHermitian ∧ (A i).rank ≤ 1) →
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        AgnosticTNS.opNorm (∑ i, ((σ i : ℝ) : ℂ) • A i) ≤
          3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i))) := by sorry

end KSPolySign
