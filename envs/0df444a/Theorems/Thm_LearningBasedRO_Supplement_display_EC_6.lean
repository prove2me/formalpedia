-- Prove2me | Theorems.Thm_LearningBasedRO_Supplement_display_EC_6
-- name    : LearningBasedRO.Supplement.display_EC_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:16:21.339936+00:00
-- url     : https://prove2.me/theorems/42502fd4-4452-4e67-9fc0-87dcec708d45
-- title:
--   (EC.6) — $\sqrt{n_2}\,(i^*/n_2-(1-\epsilon))\to\sqrt{(1-\epsilon)\epsilon}\,\Phi^{-1}(1-\delta)$, and $i^*$ is well defined for large $n_2$
-- statement:
--   Let $0<\epsilon<1$ and $0<\delta<1$, and let
--   $$i^*=\min\Big\{r:\ \sum_{k=0}^{r-1}\binom{n_2}{k}(1-\epsilon)^k\epsilon^{n_2-k}\ge1-\delta,\ 1\le r\le n_2\Big\}$$
--   be the calibration index of (4). Then the set in (4) is nonempty for all sufficiently large $n_2$, so $i^*$ is well defined, and
--   $$\sqrt{n_2}\Big(\frac{i^*}{n_2}-(1-\epsilon)\Big)\longrightarrow\sqrt{(1-\epsilon)\epsilon}\;\Phi^{-1}(1-\delta)\qquad(n_2\to\infty),$$
--   where $\Phi^{-1}$ is the inverse of the standard normal distribution function.
--
--   This locates $i^*$ to within $o(\sqrt{n_2})$ of $n_2(1-\epsilon)+\sqrt{n_2(1-\epsilon)\epsilon}\,\Phi^{-1}(1-\delta)$; both parts of Theorem 2 conclude from it.
--
--   **Formalization Note** $\sqrt{\cdot}$ is `Real.sqrt`; $\Phi^{-1}$ is the platform definition `KallMayerSLP.NormalCC.normalQuantile`.
--
--   Differences from the source:
--   - reading: ϵ, δ levels (range not stated in the theorem) → 0 < ϵ < 1, 0 < δ < 1; reason: the paper's standing range (p.1, p.5); log(1 − ϵ) and the quantiles need it
--   - reading: … → √((1 − ϵ)ϵ)Φ⁻¹(1 − δ) almost surely; i* well defined for large enough n₂ almost surely → an ordinary limit, and the set of (4) is nonempty for all large n₂; reason: i* is a deterministic function of n₂, ϵ, δ, so 'almost surely' adds nothing
--   - encoding: i* = n₂ + 1 when no r is valid (p.ec1) → the base iStar, junk value 0 when the set of (4) is empty; reason: this happens only for the finitely many n₂ < log δ / log(1 − ϵ) and does not affect the limit
--   - encoding: Φ⁻¹, the inverse standard normal distribution function → the platform definition KallMayerSLP.NormalCC.normalQuantile, inf{q : Φ(q) ≥ α}, at α = 1 − δ ∈ (0,1); reason: for α ∈ (0,1) it is the unique q with Φ(q) = α
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, proof of Theorem 2, (EC.6) and the sentence after it, p.ec2 (PDF p.37); convention for i* p.ec1 (PDF p.36)

import Mathlib
import Definitions.Def_LearningBasedRO_Model
import Definitions.Def_KallMayerSLP_NormalCC_normalQuantile

open Filter Topology

namespace LearningBasedRO.Supplement

/-- **(EC.6).** For tolerance and confidence levels `ϵ, δ ∈ (0,1)`, the calibration index `i*` of (4)
is well defined for all large `n₂`, and
`√n₂ (i*/n₂ - (1 - ϵ)) → √((1 - ϵ)ϵ) Φ⁻¹(1 - δ)` as `n₂ → ∞`,
with `Φ⁻¹` the standard normal quantile function.
Hong–Huang–Lam, arXiv:1704.04342v2, proof of Theorem 2, (EC.6) and the sentence after it,
p.ec2 (PDF p.37); convention for `i*` on p.ec1 (PDF p.36).

**Formalization Note** `i*` is a deterministic function of `n₂, ϵ, δ`, so the page's "almost
surely" adds nothing and the statement is an ordinary limit. "Well defined" means the set of (4)
is nonempty. For the finitely many `n₂` where it is empty the base `iStar` takes the junk value
`0` (the page sets `i* = n₂ + 1`); this does not affect the limit. `Φ⁻¹` is the platform's
`KallMayerSLP.NormalCC.normalQuantile`, `Φ⁻¹(α) = inf {q : Φ(q) ≥ α}`, used at `α = 1 - δ ∈ (0,1)`.
`√` is `Real.sqrt`; at `n₂ = 0` the term `i*/0` is `0` (irrelevant to the limit). -/
theorem display_EC_6 (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ᶠ n₂ : ℕ in atTop, (iStarSet n₂ ϵ δ).Nonempty) ∧
      Tendsto (fun n₂ : ℕ => Real.sqrt n₂ * ((iStar n₂ ϵ δ : ℝ) / n₂ - (1 - ϵ))) atTop
        (𝓝 (Real.sqrt ((1 - ϵ) * ϵ) * KallMayerSLP.NormalCC.normalQuantile (1 - δ))) := by sorry

end LearningBasedRO.Supplement
