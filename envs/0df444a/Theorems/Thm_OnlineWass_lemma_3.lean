-- Prove2me | Theorems.Thm_OnlineWass_lemma_3
-- name    : OnlineWass.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:45.443057+00:00
-- url     : https://prove2.me/theorems/217fe085-f854-4792-a93f-2882a52915fe
-- title:
--   Lemma 3 — $L_{\mathcal Q}$ is Lipschitz in the Wasserstein distance
-- statement:
--   Let $\mathcal Q_1,\mathcal Q_2$ be probability measures on the metric space $(\Theta,\rho)$, let $\bar p>0$, and let $\Omega_{\bar p}=[0,\bar p]^m$. Then
--
--   $$
--   \sup_{p\in\Omega_{\bar p}}\bigl|L_{\mathcal Q_1}(p)-L_{\mathcal Q_2}(p)\bigr|\le\max\{1,\bar p\}\cdot(m+1)\,\mathcal W(\mathcal Q_1,\mathcal Q_2).
--   $$
--
--   This is the only place the Wasserstein distance enters the regret analysis: it moves the dual function from the prior to the true law, at a cost linear in the budget.
--
--   **Formalization Note** The statement is for each $p\in\Omega_{\bar p}$, which is the bound on the supremum, and is an inequality in $[0,\infty]$. No convexity of $f,g$ is assumed, as the remark on p.54 allows, and no optimal coupling is assumed to exist.
--
--   Differences from the source:
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: under Assumption 1 → no convexity of f, g, 𝒳 and no (c); reason: the remark on p.54; Assumption 1 implies the hypotheses
--   - encoding: sup_{p∈Ω} of a real difference, real 𝒲 → ∀ p ∈ Ω, inequality in ℝ≥0∞; reason: a supremum is bounded iff each term is; 𝒲 is finite here
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Lemma 3, (12), p.22; proof pp.53–54

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_wasserstein
import Definitions.Def_OnlineWass_dual

open MeasureTheory

namespace OnlineWass

/-- **Lemma 3, Jiang, Li & Zhang, arXiv:2012.06961v3, p.22 (proof pp.53–54), (12):** for probability
measures `𝒬₁`, `𝒬₂` on `(Θ, 𝓑_Θ)`, `p̄ > 0` and `p ∈ Ω_p̄ = [0, p̄]ᵐ`,
`|L_𝒬₁(p) − L_𝒬₂(p)| ≤ max{1, p̄} · (m + 1) 𝒲(𝒬₁, 𝒬₂)`.

**Formalization Note.** The printed `sup_{p∈Ω_p̄}` on the left is the `∀ p ∈ Ω_p̄`. The inequality is in
`ℝ≥0∞`, where `𝒲` lives; `Assumption1ab` has no convexity, in line with the remark on p.54. -/
theorem lemma_3 {k m : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (hA : Assumption1ab M) (hρ : DistEqRho M)
    (Q₁ Q₂ : Measure Θ) [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    (pbar : ℝ) (hpbar : 0 < pbar) (p : Fin m → ℝ) (hp : p ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => pbar)) :
    ENNReal.ofReal |LQ M Q₁ p - LQ M Q₂ p| ≤
      ENNReal.ofReal (max 1 pbar * ((m : ℝ) + 1)) * wasserstein Q₁ Q₂ := by sorry

end OnlineWass
