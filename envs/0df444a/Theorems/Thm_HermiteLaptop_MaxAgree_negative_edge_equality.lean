-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_negative_edge_equality
-- name    : HermiteLaptop.MaxAgree.negative_edge_equality
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:17:29.419333+00:00
-- url     : https://prove2.me/theorems/fadf6511-4703-4462-946a-c1ad20adfb96
-- title:
--   §4.3, negative-edge equality — 1 − P(0) = 1 − (0.364/4 + 0.636/5) = 0.7818 for the 4/5-spokes mixture
-- statement:
--   For the mixture of the 4-spokes and 5-spokes roundings with probabilities $\lambda_4=0.364$ and $\lambda_5=0.636$, with $a=0$,
--   $$1-P(a)=1-P(0)=1-\big(0.364\,P_4(0)+0.636\,P_5(0)\big)=1-\Big(\frac{0.364}4+\frac{0.636}5\Big)=0.7818.$$
--   This is the negative-edge inequality of the edge-wise analysis with equality, shown analytically from Eq. (10).
--
--   **Formalization Note.** The mixture is any `Mixture` with `lam 4 = 0.364`, `lam 5 = 0.636` (all other weights are then zero). The three equalities are stated as a conjunction.
--
--   Differences from the source:
--   - encoding: the mixture of 4- and 5-spokes with probabilities 0.364 and 0.636 → any Mixture with λ_4 = 0.364 and λ_5 = 0.636; reason: since λ ≥ 0 sums to 1, all other λ_k vanish: the same mixture
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 29 (PDF 32), §4.3 (display before Theorem 4.5)

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Mixture

namespace HermiteLaptop.MaxAgree

/-- §4.3, negative-edge equality: for the mixture with `λ_4 = 0.364`, `λ_5 = 0.636`,
`1 − P(0) = 1 − (0.364 P_4(0) + 0.636 P_5(0)) = 1 − (0.364/4 + 0.636/5) = 0.7818`. -/
theorem negative_edge_equality (μ : Mixture) (h4 : μ.lam 4 = 0.364) (h5 : μ.lam 5 = 0.636) :
    1 - μ.collision 0 = 1 - (0.364 * collisionProb 4 0 + 0.636 * collisionProb 5 0) ∧
    0.364 * collisionProb 4 0 + 0.636 * collisionProb 5 0 = 0.364 / 4 + 0.636 / 5 ∧
    (1 : ℝ) - (0.364 / 4 + 0.636 / 5) = 0.7818 := by sorry

end HermiteLaptop.MaxAgree
