-- Prove2me | Theorems.Thm_MinSumFPT_core_bound
-- name    : MinSumFPT.core_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:17.826812+00:00
-- url     : https://prove2.me/theorems/502900ab-4bfc-4a87-ab06-d6cae8ea6c44
-- title:
--   §2.1 — $|\mathrm{core}_\alpha(C)|>(1-\alpha^{-1})|C|$
-- statement:
--   Let $d$ be a pseudometric on $A$, $C\subseteq A$ a nonempty cluster and $\alpha>1$. With $\mathrm{core}_\alpha(C)=\{x\in C:\|e_x-\mu_C\|_{W_1}\le\alpha\Delta_C\}$,
--
--   $$
--   |\mathrm{core}_\alpha(C)|>(1-\alpha^{-1})\cdot|C| .
--   $$
--
--   This is Markov's inequality for the distances to $\mu_C$. In particular $\mathrm{core}_2(C)$ contains more than half of $C$, which is what the sampling lemmas use.
--
--   Differences from the source:
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
--   - encoding: a cluster C → a nonempty Finset C; reason: µ_C and Δ_C divide by |C|; excludes only undefined cases
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §2.1, core bound, p.8

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_Delta

namespace MinSumFPT

/-- §2.1, the core bound (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §2.1, p.8): for `α > 1` and a nonempty cluster `C`,
`core_α(C) = {x ∈ C : ‖e_x − µ_C‖_{W₁} ≤ α ⋅ Δ_C}` has `|core_α(C)| > (1 − α⁻¹) ⋅ |C|`. -/
theorem core_bound {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsPseudometric d)
    (α : ℝ) (hα : 1 < α) (C : Finset (Fin n)) (hC : C.Nonempty) :
    (1 - α⁻¹) * (C.card : ℝ) < ((core d α C).card : ℝ) := by sorry

end MinSumFPT
