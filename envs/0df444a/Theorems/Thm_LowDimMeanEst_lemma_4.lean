-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_4
-- name    : LowDimMeanEst.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:52:17.99342+00:00
-- url     : https://prove2.me/theorems/10cf1910-118f-4dce-865e-88e9f5c1671f
-- title:
--   Lemma 4 — Algorithm 2 is scale invariant: the same outputs on $X$ and $aX$ for $a>0$
-- statement:
--   **Lemma 4.** Let $X=(x_1,\dots,x_N)$ be samples in $\mathbb R^d$, $\delta\in(0,1)$ and $a>0$. Then $w$ is an output of Algorithm 2 on $(aX,\delta)$ if and only if it is an output on $(X,\delta)$.
--
--   Together with Lemma 5 this lets the analysis assume that the data distribution has covariance $\Sigma\preceq I$.
--
--   **Formalization Note** Algorithm 2 is a relation (Definition `Algorithm2`), so "the output is the same" is the equality of the two sets of outputs.
--
--   Differences from the source:
--   - generalization: Algorithm 2 as printed → the corrected relation IsTrimOutput (correction C1 of Lemma 3); reason: on inputs where the printed search has an output the two have the same outputs, so the statement specializes to the source's
--   - encoding: "the output is the same" → the sets of outputs coincide; reason: Algorithm 2 is a relation
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 4, p.9 (restated p.50)

import Mathlib
import Definitions.Def_LowDimMeanEst_Algorithm2

namespace LowDimMeanEst

/-- **Lemma 4**, p.9 (restated p.50).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Suppose X is a set of samples in ℝᵈ. Then for any δ ∈ (0, 1) and any scale a > 0, the output of
Algorithm 2 is the same when run on both X and aX."

**Formalization Note.** Algorithm 2 is the relation `IsTrimOutput` (correction C1), so "the output
is the same" is the equality of the two sets of outputs.
-/
theorem lemma_4 {d N : ℕ} (x : Fin N → E d) (δ a : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ha : 0 < a)
    (w : Fin N → ℝ) : IsTrimOutput (a • x) δ w ↔ IsTrimOutput x δ w := by sorry

end LowDimMeanEst
