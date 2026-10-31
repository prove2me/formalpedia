-- Prove2me | Theorems.Thm_KallMayerSLP_RiskMeasures_proposition_7_3
-- name    : KallMayerSLP.RiskMeasures.proposition_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:41:56.953134+00:00
-- url     : https://prove2.me/theorems/63f50917-23cb-43a7-909e-db3fd1e29b4e
-- title:
--   Proposition 7.3 — expectation, the worst case $\rho_{\mathrm{fat}}$ and CVaR are coherent and convex risk measures
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space. Each of the following risk measures is positive homogeneous, subadditive, monotonically increasing and translation invariant; consequently it is a convex risk measure in the sense of the axioms (7.3) and, being positively homogeneous, a coherent risk measure in the sense of the axioms (7.2):
--
--   1. (A) the expectation $\rho_{\mathrm E}(\vartheta):=\mathbb E[\vartheta]$ on $\mathcal L^1_1$;
--   2. (B) the worst case $\rho_{\mathrm{fat}}(\vartheta):=\max_{\hat\vartheta\in\Theta}\hat\vartheta$ on $\mathcal L^\infty_1$, where $\Theta$ is the support of $\vartheta$;
--   3. (C) for every $0<\alpha<1$, the conditional value-at-risk on $\mathcal L^1_1$,
--   $$
--   \rho^\alpha_{\mathrm{CVaR}}(\vartheta):=\min_{z}\Big[z+\frac1{1-\alpha}\,\mathbb E\big[(\vartheta-z)^+\big]\Big].
--   $$
--
--   By Proposition 7.2, each of them therefore turns a linear-affine random variable $\eta^\top x-\xi$ into a convex evaluation function.
--
--   **Formalization Note** Coherence bundles (A1)–(A4) and so contains the four listed properties. The monotonicity hypothesis $\vartheta_1\le\vartheta_2$ is almost sure. The maximum in (B) and the minimum in (C) are a supremum and an infimum (see the definitions of $\rho_{\mathrm{fat}}$ and $\rho^\alpha_{\mathrm{CVaR}}$); for the random variables in question both are attained.
--
--   Differences from the source:
--   - generalization: ϑ₁ ≤ ϑ₂ in (A3), (F2): pointwise, "ϑ₁(ω) ≤ ϑ₂(ω) for all ω" in the proof of (B), p.185 → ϑ₁ ≤ ϑ₂ almost surely; reason: a weaker hypothesis than the pointwise order of the book's proof ("ϑ₁(ω) ≤ ϑ₂(ω) for all ω"), so the monotonicity clause implies the book's
--   - encoding: 𝓛^p₁ (p = 1, 2, ∞) of (1.6) → Lspace ℝ p P: functions Ω → ℝ with MemLp · p P, a submodule of Ω → ℝ; reason: random variables with finite p-th moment (resp. bounded support); same instances
--   - encoding: max over the support Θ in (B); min over z in (C) → sSup of the topological support of the law P.map ϑ; real infimum ⨅ z; reason: both are attained for ϑ ∈ 𝓛^∞₁, resp. ϑ ∈ 𝓛¹₁ and 0 < α < 1 (§4.3), so the values agree
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.3, p.184 (PDF 194); axioms (7.2), (7.3), p.183 (PDF 193)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_Lspace
import Definitions.Def_KallMayerSLP_RiskMeasures_IsCoherentRiskMeasure
import Definitions.Def_KallMayerSLP_RiskMeasures_IsConvexRiskMeasure
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoE
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoFat
import Definitions.Def_KallMayerSLP_RiskMeasures_cvar

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Proposition 7.3** (expectation, worst case and CVaR are coherent and convex risk measures).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.3, p.184 (PDF 194). The following risk measures are positive homogeneous and
subadditive, monotonically increasing and translation invariant; consequently they are convex
risk measures (axioms (7.3)) and coherent risk measures (axioms (7.2)):
(A) `ρ_E(ϑ) := 𝔼[ϑ]`, `ϑ ∈ 𝓛¹₁`;
(B) `ρ_fat(ϑ) := max_{ϑ̂ ∈ Θ} ϑ̂`, `ϑ ∈ 𝓛^∞₁`, `Θ` the support of `ϑ`;
(C) `ρ^α_CVaR(ϑ) := min_z [z + (1/(1 − α)) 𝔼[(ϑ − z)⁺]]`, `ϑ ∈ 𝓛¹₁`, `0 < α < 1`.

**Formalization Note.** `(Ω, 𝓕, P)` is an arbitrary probability space; `𝓛^p₁` is `Lspace ℝ p P`
(random variables `Ω → ℝ` with `MemLp · p P`). Coherence bundles (A1)–(A4), so it contains the
four properties listed first. The hypothesis of monotonicity is `ϑ₁ ≤ ϑ₂` almost surely, weaker
than the pointwise order used in the book's proof, so the statement is stronger. The `max` in (B) and the
`min` in (C) are `sSup` and `⨅` (see the definitions). -/
theorem proposition_7_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    (IsCoherentRiskMeasure P (Lspace ℝ 1 P) (rhoE P) ∧
      IsConvexRiskMeasure P (Lspace ℝ 1 P) (rhoE P)) ∧
    (IsCoherentRiskMeasure P (Lspace ℝ ⊤ P) (rhoFat P) ∧
      IsConvexRiskMeasure P (Lspace ℝ ⊤ P) (rhoFat P)) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      IsCoherentRiskMeasure P (Lspace ℝ 1 P) (cvar P α) ∧
        IsConvexRiskMeasure P (Lspace ℝ 1 P) (cvar P α)) := by sorry

end KallMayerSLP.RiskMeasures
