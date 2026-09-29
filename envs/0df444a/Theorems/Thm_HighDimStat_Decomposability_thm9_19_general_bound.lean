-- Prove2me | Theorems.Thm_HighDimStat_Decomposability_thm9_19_general_bound
-- name    : HighDimStat.Decomposability.thm9_19_general_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:17:06.145091+00:00
-- url     : https://prove2.me/theorems/4f8b763e-e706-4b80-903a-b0930ecc9d99
-- title:
--   Bounds for general decomposable M-estimators (Theorem 9.19)
-- statement:
--   **Theorem 9.19 ("Bounds for general models").** The chapter's central result: a deterministic
--   error bound for the regularized M-estimator that holds under any restricted-strong-convexity
--   certificate and any decomposable regularizer, for *any* choice of the model subspace pair
--   subject to two explicit side conditions.
--
--   Assume (A1) $L_n$ is convex and satisfies the restricted strong convexity condition (Def.
--   9.15) with curvature $\kappa>0$, radius $R$ and tolerance $\tau_n^2$, with respect to a norm
--   $\|\cdot\|$ induced by the inner product on $\Omega$; and (A2) the regularizer $\Phi$ is
--   decomposable with respect to a subspace pair $(\mathcal M,\bar{\mathcal M})$. Let $\hat\theta$
--   be any optimal solution of the M-estimator, conditioned on the good event
--   $\mathcal G(\lambda_n)$. Then:
--
--   $$
--   \text{(a)}\quad \Phi(\hat\theta-\theta^*) \le 4\Big(\Psi(\bar{\mathcal M})\,
--   \|\hat\theta-\theta^*\| + \Phi(\theta^*_{\mathcal M^\perp})\Big).
--   $$
--
--   $$
--   \text{(b)}\quad \text{if } \tau_n^2\Psi^2(\bar{\mathcal M}) \le \kappa/64 \text{ and }
--   \varepsilon_n(\mathcal M,\bar{\mathcal M}) \le R, \text{ then } \|\hat\theta-\theta^*\|^2 \le
--   \varepsilon_n^2(\mathcal M,\bar{\mathcal M}).
--   $$
--
--   where $\varepsilon_n^2(\mathcal M,\bar{\mathcal M}) := \frac{9\lambda_n^2}{\kappa^2}
--   \Psi^2(\bar{\mathcal M}) + \frac{8}{\kappa}\big(\lambda_n\Phi(\theta^*_{\mathcal M^\perp}) +
--   16\tau_n^2\Phi^2(\theta^*_{\mathcal M^\perp})\big)$ (Eq. (9.47)).
--
--   As the book itself remarks, this claim is *deterministic*: probability enters only in
--   certifying the RSC condition and the good event, separately, for a specific statistical
--   model.
--
--   **Formalization Note** Both parts (a) and (b) are packaged as one conjunction (`main_item`
--   of this mission). `Ψ(bar M)` (`subspaceLip Φ Mbar`) is used throughout — `source.pdf` pages
--   300/301, rendered and inspected directly, print the bar over `M̄` clearly in equations
--   (9.47)-(9.48) (the *derived* `source.txt` extraction drops the diacritic, not the PDF
--   itself), independently confirmed by checking the book's own proof, which applies the
--   subspace Lipschitz constant to $\Delta_{\bar{\mathcal M}}\in\bar{\mathcal M}$ — see `Core`'s
--   Formalization Note. `hκ : 0 < κ` and `hR : 0 < R` make explicit the positivity Definition
--   9.15 states jointly for $\kappa$ and $R$ ("with radius $R>0$, curvature $\kappa>0$"), and
--   `hlam : 0 < lamN` the chapter's standing convention that $\lambda_n$ is a (positive)
--   regularization weight; none of the three narrows the theorem's actual scope (see
--   `MODERATION_NOTES.md`).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 280 (PDF p. 300), Theorem 9.19, Eqs. (9.46)-(9.48)

import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

/-- Theorem 9.19 ("Bounds for general models", p. 280): under (A1) — `Ln` convex and satisfying
restricted strong convexity with curvature `κ`, tolerance `τn²` and radius `R` — and (A2) — `Φ`
decomposable with respect to `(M, M̄)` — conditioned on the good event `G(λn)`:
(a) any optimal solution `θ̂` of the M-estimator satisfies
`Φ(θ̂ - θ*) ≤ 4(Ψ(M̄) ‖θ̂ - θ*‖ + Φ(θ*_{Mᗮ}))`;
(b) whenever `τn² Ψ(M̄)² ≤ κ/64` and `εn(M, M̄) ≤ R`, `‖θ̂ - θ*‖² ≤ εn²(M, M̄)`. -/
theorem thm9_19_general_bound
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN κ τnSq R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hRSC : RSC Ln g θstar Φ κ τnSq R)
    (hκ : 0 < κ) (hR : 0 < R) (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (htol : τnSq * subspaceLip Φ Mbar ^ 2 ≤ κ / 64)
    (hRbound : Real.sqrt (epsilonSq Φ M Mbar θstar lamN κ τnSq) ≤ R) :
    Φ (θhat - θstar) ≤
        4 * (subspaceLip Φ Mbar * ‖θhat - θstar‖ + Φ (Mᗮ.starProjection θstar)) ∧
      ‖θhat - θstar‖ ^ 2 ≤ epsilonSq Φ M Mbar θstar lamN κ τnSq := by sorry

end HighDimStat.Decomposability
