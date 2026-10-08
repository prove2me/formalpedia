-- Prove2me | Theorems.Thm_GenEmpLik_Expansion_lemma_9
-- name    : GenEmpLik.Expansion.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:48:08.004132+00:00
-- url     : https://prove2.me/theorems/5ccbce89-3f81-453c-956e-6b60fb48342e
-- title:
--   Lemma 9 — the supremum of $u^Tz$ over $\mathcal U_{\rm big}$ is at most $\sqrt{\rho s_n(z)^2/n}/\sqrt{1-C\epsilon}$
-- statement:
--   Let $n\ge1$, $\rho>0$, $\epsilon>0$, $C\ge0$ with $C\epsilon<1$, and $z\in\mathbb R^n$, with $\bar z_n$, $s_n(z)^2$ as in Lemma 8. If
--
--   $$
--   \frac{\|z-\bar z_n\mathbb 1\|_\infty}{\sqrt n}\le\epsilon\, s_n(z)\sqrt{\frac{1-C\epsilon}{\rho}},
--   $$
--
--   then
--
--   $$
--   \sup_{u\in\mathcal U_{\rm big}}u^Tz\le\sqrt{\frac\rho n s_n(z)^2}\cdot\frac{1}{\sqrt{1-C\epsilon}},
--   $$
--
--   where $\mathcal U_{\rm big}=\{u:\mathbb 1^Tu=0,\ \sum_i h_\epsilon(nu_i)\le\rho/(2(1-C\epsilon))\}$ is the big set of (31) and $h_\epsilon$ the Huber function. This is the upper half of the sandwich for the robust mean.
--
--   **Formalization Note** The hypothesis $C\epsilon<1$ is implicit in the paper (it is needed for $\sqrt{1-C\epsilon}$ and for $\mathcal U_{\rm big}$ to be the intended set). Conventions as in Lemma 8; the supremum is a real `sSup` of a non-empty set that is bounded because $h_\epsilon$ grows linearly.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, pp. 32–33, Lemma 9

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_reparamSets
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar

open VarianceRegularization.Expansion

namespace GenEmpLik.Expansion

/-- Lemma 9 (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, pp. 32–33). Let `s_n(z)² = \overline{z²}_n − z̄_n²`
(`empVar z`). If `Cε < 1` and `‖z − z̄_n‖_∞ / √n ≤ ε s_n(z) √((1 − Cε)/ρ)`, then
`sup_{u ∈ 𝒰_big} uᵀz ≤ √(ρ/n · s_n(z)²) · 1/√(1 − Cε)`. -/
theorem lemma_9 {n : ℕ} (hn : 0 < n) {ρ ε C : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hC : 0 ≤ C)
    (hCε : C * ε < 1) (z : Fin n → ℝ)
    (hz : (⨆ i, |z i - empMean z|) / Real.sqrt n ≤
      ε * Real.sqrt (empVar z) * Real.sqrt ((1 - C * ε) / ρ)) :
    sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Ubig n ε C ρ) ≤
      Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 - C * ε)) := by sorry

end GenEmpLik.Expansion
