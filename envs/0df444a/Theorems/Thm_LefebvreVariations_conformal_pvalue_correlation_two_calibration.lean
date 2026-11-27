-- Prove2me | Theorems.Thm_LefebvreVariations_conformal_pvalue_correlation_two_calibration
-- name    : LefebvreVariations.conformal_pvalue_correlation_two_calibration
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:27:47.464052+00:00
-- url     : https://prove2.me/theorems/9d75865c-7e70-44e4-9000-a60d9fffc77e
-- title:
--   Lefebvre's variations, No. 275 — on a theme by Bates, Candes, Lei, Romano and Sesia: the conformal p-values of two test points have correlation 1/4 for two calibration scores
-- statement:
--   Let $\sigma$ be uniformly distributed on the permutations of $\{0,1,2,3\}$, regarded as the ranks of four scores with no ties; points $0,1$ are calibration points and points $2,3$ are test points. For $j\in\{0,1\}$ set
--   $$
--   p_j=\frac{1+\#\{i\in\{0,1\}:\ \sigma(2+j)\le\sigma(i)\}}{3}.
--   $$
--   Then
--   $$
--   \operatorname{Var}(p_0)=\operatorname{Var}(p_1)=\frac{2}{27},\qquad \operatorname{Cov}(p_0,p_1)=\frac1{54},
--   $$
--   so that $\operatorname{Corr}(p_0,p_1)=\tfrac14=\tfrac1{n+2}$ for $n=2$ calibration scores.
--
--   For scores of exchangeable continuous null points, the conformal p-values of two test points share the same calibration sample and are therefore positively correlated; the general statement is that the pairwise correlation is $1/(n+2)$ for every $n$. Only the ranks matter, so for $n=2$ and two test points the claim reduces to the finite computation above.
--
--   **Formalization Note** The expectation is the average over `Equiv.Perm (Fin 4)` (24 permutations) of rational numbers; calibration index `i : Fin 2` is `Fin.castAdd 2 i` and test index `j` is `Fin.natAdd 2 j`. The p-value counts calibration scores that are at least the test score, as in the standard conformal p-value. Variances and covariance are written out as `E[X²] - E[X]²` and `E[XY] - E[X]E[Y]`.
--
--   **Why this is a variation.** A variation on the open platform problem ConformalOutlierTesting.pairwise_correlation (null conformal p-values have pairwise correlation 1/(n+2)), played at n = 2 calibration scores and two test points, for the identity function G and with the exchangeable continuous scores replaced by a uniform ordering of ranks. It is a special case in distribution, not a formal consequence of the parent as formalised there with general measures.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Bates, Candes, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, Annals of Statistics 51(1) (2023), arXiv:2104.08279 (paper identity confirmed; the Lemma 1 / Section 2.1 location is as recorded by the platform's parent statement, not re-read). Checked here in exact rational arithmetic over all 24 permutations: variances 2/27 and 2/27, covariance 1/54, correlation 1/4.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Conformal p-values with `n = 2` calibration scores and two test points, all four scores in uniformly random order (no ties).
Indices `0, 1` are the calibration points and `2, 3` the test points; the score of point `i` is `σ i` for a uniform `σ ∈ S₄`, and the conformal p-value of test point `j` is `(1 + #{calibration scores ≥ its score}) / 3`. The two p-values each have variance `2/27` and covariance `1/54`, so their correlation is `1/4 = 1/(n + 2)`.
Source: Bates, Candès, Lei, Romano, Sesia, *Testing for Outliers with Conformal p-values*, arXiv:2104.08279, Section 2.1, Lemma 1, as recorded by the platform (not re-read). -/
theorem conformal_pvalue_correlation_two_calibration :
    let p : Equiv.Perm (Fin 4) → Fin 2 → ℚ := fun σ j =>
      (1 + (((Finset.univ : Finset (Fin 2)).filter
        fun i => σ (Fin.natAdd 2 j) ≤ σ (Fin.castAdd 2 i)).card : ℚ)) / 3
    let E : (Equiv.Perm (Fin 4) → ℚ) → ℚ := fun f => (∑ σ, f σ) / 24
    (E (fun σ => p σ 0 ^ 2) - E (fun σ => p σ 0) ^ 2 = 2 / 27) ∧
    (E (fun σ => p σ 1 ^ 2) - E (fun σ => p σ 1) ^ 2 = 2 / 27) ∧
    (E (fun σ => p σ 0 * p σ 1) - E (fun σ => p σ 0) * E (fun σ => p σ 1) = 1 / 54) := by
  sorry

end LefebvreVariations
