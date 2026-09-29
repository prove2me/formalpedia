-- Prove2me | Theorems.Thm_HighDimStat_Decomposability_cor9_20_special_case
-- name    : HighDimStat.Decomposability.cor9_20_special_case
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:17:36.045701+00:00
-- url     : https://prove2.me/theorems/2193dcbf-a9f0-4fd5-83ed-ad1ea0c91c81
-- title:
--   The oracle bound when the truth lies exactly in the model subspace (Corollary 9.20)
-- statement:
--   **Corollary 9.20.** When the target parameter lies exactly in the model subspace, Theorem
--   9.19's family of bounds collapses to a single, purely multiplicative estimation-error bound
--   — the approximation-error term of Eq. (9.47) vanishes entirely.
--
--   Under the hypotheses of Theorem 9.19, suppose in addition that $\theta^*\in\mathcal M$. Then
--   any optimal solution $\hat\theta$ of the M-estimator satisfies
--
--   $$
--   \Phi(\hat\theta-\theta^*) \le \frac{6\lambda_n}{\kappa}\Psi^2(\bar{\mathcal M}), \qquad
--   \|\hat\theta-\theta^*\|^2 \le \frac{9\lambda_n^2}{\kappa^2}\Psi^2(\bar{\mathcal M}).
--   $$
--
--   This is the form of the bound used directly to obtain concrete, closed-form error rates for
--   every specific model considered later in the chapter (sparse GLMs, group Lasso, low-rank
--   matrix regression in Chapter 10), since the true parameter is exactly $s$-sparse, exactly
--   group-sparse, or exactly low rank in each such application.
--
--   **Formalization Note** Same standing hypotheses as Theorem 9.19 (`hRSC`, `hκ`, `hR`, `hlam`,
--   `hopt`, `hG`, `htol`, `hRbound`), plus `hθM : θstar ∈ M`. `Ψ(bar M)` used throughout, per the
--   same overbar resolution as `thm9_19_general_bound`.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 281 (PDF p. 301), Corollary 9.20, Eqs. (9.49a)-(9.49b)

import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

/-- Corollary 9.20 (p. 281): in addition to the conditions of Theorem 9.19, suppose the target
`θ*` belongs to the model subspace `M`. Then any optimal solution `θ̂` of the M-estimator
satisfies both `Φ(θ̂ - θ*) ≤ 6λn/κ · Ψ(M̄)²` and `‖θ̂ - θ*‖² ≤ 9λn²/κ² · Ψ(M̄)²`. -/
theorem cor9_20_special_case
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN κ τnSq R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hRSC : RSC Ln g θstar Φ κ τnSq R)
    (hκ : 0 < κ) (hR : 0 < R) (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (htol : τnSq * subspaceLip Φ Mbar ^ 2 ≤ κ / 64)
    (hRbound : Real.sqrt (epsilonSq Φ M Mbar θstar lamN κ τnSq) ≤ R)
    (hθM : θstar ∈ M) :
    Φ (θhat - θstar) ≤ 6 * lamN / κ * subspaceLip Φ Mbar ^ 2 ∧
      ‖θhat - θstar‖ ^ 2 ≤ 9 * lamN ^ 2 / κ ^ 2 * subspaceLip Φ Mbar ^ 2 := by sorry

end HighDimStat.Decomposability
