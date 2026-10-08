-- Prove2me | Theorems.Thm_GenEmpLik_Expansion_lemma_8
-- name    : GenEmpLik.Expansion.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:48:01.681356+00:00
-- url     : https://prove2.me/theorems/bd512a7b-7aec-4d0b-a17e-60daecdf4ab1
-- title:
--   Lemma 8 — the supremum of $u^Tz$ over $\mathcal U_{\rm sm}$ equals $\sqrt{\rho s_n(z)^2/n}/\sqrt{1+C\epsilon}$
-- statement:
--   Let $n\ge1$, $\rho>0$, $\epsilon>0$, $C\ge0$ and $z\in\mathbb R^n$. Write $\bar z_n=\frac1n\sum_i z_i$, $\overline{z^2}_n=\frac1n\sum_i z_i^2$ and $s_n(z)^2=\overline{z^2}_n-\bar z_n^2$. If
--
--   $$
--   \frac{\|z-\bar z_n\mathbb 1\|_\infty}{\sqrt n}\le\epsilon\, s_n(z)\sqrt{\frac{1+C\epsilon}{\rho}},
--   $$
--
--   then
--
--   $$
--   \sup_{u\in\mathcal U_{\rm sm}}u^Tz=\sqrt{\frac\rho n s_n(z)^2}\cdot\frac{1}{\sqrt{1+C\epsilon}},
--   $$
--
--   where $\mathcal U_{\rm sm}=\{u:\mathbb 1^Tu=0,\ \|nu\|_\infty\le\epsilon,\ (1+C\epsilon)\|nu\|_2^2\le\rho\}$ is the small set of (31). This is the lower half of the sandwich for the robust mean.
--
--   **Formalization Note** $\bar z_n$ and $s_n(z)^2$ are the published `empMean` and `empVar` ($1/n$ normalisation); $s_n(z)=\sqrt{s_n(z)^2}$; $\|z-\bar z_n\mathbb 1\|_\infty$ is `⨆ i, |z i - empMean z|`. The supremum is a real `sSup` of a non-empty bounded set.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 32, Lemma 8

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_reparamSets
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar

open VarianceRegularization.Expansion

namespace GenEmpLik.Expansion

/-- Lemma 8 (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 32). Let `s_n(z)² = \overline{z²}_n − z̄_n²`
(`empVar z`). If `‖z − z̄_n‖_∞ / √n ≤ ε s_n(z) √((1 + Cε)/ρ)`, then
`sup_{u ∈ 𝒰_sm} uᵀz = √(ρ/n · s_n(z)²) · 1/√(1 + Cε)`. -/
theorem lemma_8 {n : ℕ} (hn : 0 < n) {ρ ε C : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hC : 0 ≤ C)
    (z : Fin n → ℝ)
    (hz : (⨆ i, |z i - empMean z|) / Real.sqrt n ≤
      ε * Real.sqrt (empVar z) * Real.sqrt ((1 + C * ε) / ρ)) :
    sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Usm n ε C ρ) =
      Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 + C * ε)) := by sorry

end GenEmpLik.Expansion
