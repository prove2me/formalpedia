-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_D_2
-- name    : OfflineCensoredPricing.Identifiability.lemma_D_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:23.652909+00:00
-- url     : https://prove2.me/theorems/a9c40340-f421-494a-830b-b5801f6f6216
-- title:
--   Lemma D.2, p. 45 — |γ̂ − γ| ≤ α with probability at least 1 − 2Ke^{−2Nα²}
-- statement:
--   Fix an instance satisfying the standing assumptions, with $\gamma = \mathbb P[\xi < \lambda] = \max_i\gamma_i$ and data size $N = \min_i N_i$. Let $\hat\gamma = \max_i \hat\gamma_i$, where $\hat\gamma_i = \frac1{N_i}\sum_j \mathbb 1\{S^j_i < y_i\}$ is the empirical uncensored fraction at the $i$-th price. For any $\alpha > 0$, with probability at least $1 - 2Ke^{-2N\alpha^2}$,
--   $$|\hat\gamma - \gamma| \le \alpha.$$
--
--   The empirical uncensored degree $\hat\gamma$ enters the estimated optimistic revenue $\hat R_1$; this lemma controls that error in the proof of Lemma 2.
--
--   **Formalization Note** The outer probability of $\{|\hat\gamma - \gamma| > \alpha\}$ is bounded by $2Ke^{-2N\alpha^2}$.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 45, Lemma D.2 (proof Appendix D.5, p. 53)

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Lemma D.2** (Convergence of empirical uncensored degree, p. 45). For any `α > 0`, with
probability at least `1 − 2K e^{−2Nα²}`, `|γ̂ − γ| ≤ α`, where `γ̂ = maxᵢ γ̂ᵢ` and `γ = P[ξ < λ]`. -/
theorem lemma_D_2 {K : ℕ} (I : Instance K) (hI : I.Standing) (Nv : Fin K → ℕ) {α : ℝ}
    (hα : 0 < α) :
    dataLaw I Nv {ω | α < |gammaHatMax I.toPublic (sales I ω) - gam I|} ≤
      ENNReal.ofReal (2 * K * Real.exp (-(2 * (Nmin Nv : ℝ) * α ^ 2))) := by sorry

end OfflineCensoredPricing.Identifiability
