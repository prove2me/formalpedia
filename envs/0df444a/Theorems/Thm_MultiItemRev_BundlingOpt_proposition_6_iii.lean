-- Prove2me | Theorems.Thm_MultiItemRev_BundlingOpt_proposition_6_iii
-- name    : MultiItemRev.BundlingOpt.proposition_6_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:27:30.190865+00:00
-- url     : https://prove2.me/theorems/3bb3aaae-6f86-4107-a513-f8815655c035
-- title:
--   Proposition 6 (iii), p. 14 — Rev(X) is the supremum of R(µ;X) over IC, IR and NPT mechanisms
-- statement:
--   Let $X$ be a $k$-good random valuation with $k \ge 1$ with law $\mu$ on $\mathbb{R}^k_+$. Then the optimal revenue is already attained in the supremum over mechanisms with no positive transfer:
--   $$\mathrm{Rev}(X) = \sup\bigl\{\, R(\mu'; X) \ :\ \mu' \text{ admissible (IC, IR) and NPT} \,\bigr\}.$$
--
--   Restricting to NPT mechanisms ($s \ge 0$) is what allows the proof of Theorem 16 to truncate revenue integrals without sign issues.
--
--   **Formalization Note** Each revenue is clipped at $0$ inside the supremum, exactly as in the definition of $\mathrm{Rev}$; for NPT mechanisms $R(\mu';X) \ge 0$, so the clip is inactive there.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 14, Proposition 6 (iii)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt

theorem proposition_6_iii {ι : Type*} [Fintype ι] [Nonempty ι] (μ : Measure (ι → ℝ≥0))
    [IsProbabilityMeasure μ] :
    Rev μ = ⨆ (M : Mechanism ι) (_ : IsAdmissible M ∧ IsNPT M), (expRevenue μ M).toENNReal := by sorry

end MultiItemRev.BundlingOpt
