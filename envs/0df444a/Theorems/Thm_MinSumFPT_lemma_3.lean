-- Prove2me | Theorems.Thm_MinSumFPT_lemma_3
-- name    : MinSumFPT.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:08.799516+00:00
-- url     : https://prove2.me/theorems/283d6d5f-1cf0-4862-a589-50384a999709
-- title:
--   Lemma 3 — $\mathrm{cost}(C)=|C|\sum_{x\in C}\|e_x-\mu_C\|_{W_1}=|C|^2\Delta_C$
-- statement:
--   Let $d$ be a pseudometric on $A$ and $C\subseteq A$ a nonempty cluster, with $\mu_C$ the uniform distribution on $C$ and $\Delta_C=\frac1{|C|}\sum_{x\in C}\|e_x-\mu_C\|_{W_1}$. Then
--
--   $$
--   \mathrm{cost}(C)=\sum_{x,y\in C}d(x,y)=|C|\cdot\sum_{x\in C}\|e_x-\mu_C\|_{W_1}=|C|^2\cdot\Delta_C .
--   $$
--
--   So a cluster's cost is $|C|^2$ times the average distance of its points to the center $\mu_C$ in $W_1(A,d)$. This identity turns cost bounds into distance bounds throughout the analysis.
--
--   Differences from the source:
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
--   - encoding: a cluster C → a nonempty Finset C; reason: µ_C and Δ_C divide by |C|; excludes only undefined cases
--   - encoding: the norm with unit ball conv{(e_x − e_y)/d(x,y)} → the flow form PerturbedWF.transNorm; reason: equal for a metric; the extension for a pseudometric, where the unit-ball formula divides by 0
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 3, p.8

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumFPT_Delta

namespace MinSumFPT

/-- Lemma 3 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 3, p.8): for a nonempty cluster `C`, with `µ_C` the uniform
distribution on `C` and `Δ_C = (1/|C|) ∑_{x∈C} ‖e_x − µ_C‖_{W₁}`,
`cost(C) = |C| ⋅ ∑_{x∈C} ‖e_x − µ_C‖_{W₁} = |C|² ⋅ Δ_C`.

**Formalization Note.** `cost(C) = ∑_{x,y∈C} d(x,y)` over ordered pairs (`MinSumClust.cost`);
`C` is nonempty because µ_C divides by `|C|`. -/
theorem lemma_3 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsPseudometric d)
    (C : Finset (Fin n)) (hC : C.Nonempty) :
    MinSumClust.cost d C =
        (C.card : ℝ) * ∑ x ∈ C, PerturbedWF.transNorm d (unitVec x - centroid C) ∧
      (C.card : ℝ) * ∑ x ∈ C, PerturbedWF.transNorm d (unitVec x - centroid C) =
        (C.card : ℝ) ^ 2 * Delta d C := by sorry

end MinSumFPT
