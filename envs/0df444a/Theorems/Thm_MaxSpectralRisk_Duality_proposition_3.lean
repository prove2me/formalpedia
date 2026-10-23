-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_proposition_3
-- name    : MaxSpectralRisk.Duality.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:21.043992+00:00
-- url     : https://prove2.me/theorems/a4207ba2-2bf7-4a91-86d5-e5e81add1114
-- title:
--   Proposition 3, p. 11 — inf_{β∈L¹(γσ)} max_{π∈Π(µ,ν)} H(π, β) = max_{π∈Π(µ,ν)} inf_{β∈L¹(γσ)} H(π, β)
-- statement:
--   Throughout, $\mathcal X$ and $\mathcal Y$ are Polish spaces with their Borel $\sigma$-algebras, $\mu$ and $\nu$ are Borel probability measures on them, $\Pi(\mu,\nu)$ is the set of couplings, $\sigma$ is a bounded, right-continuous spectral function (A.4), and $L:\mathcal X\times\mathcal Y\to\mathbb R$ is the loss. Assume A.1–A.3 and let $H$ be as in Proposition 2. Then for every $\beta\in\mathcal L^1(\gamma_\sigma)$ the supremum of $H(\cdot,\beta)$ over $\Pi(\mu,\nu)$ is attained, the supremum over $\Pi(\mu,\nu)$ of $\pi\mapsto\inf_{\beta\in\mathcal L^1(\gamma_\sigma)}H(\pi,\beta)$ is attained, and
--   $$\inf_{\beta\in\mathcal L^1(\gamma_\sigma)}\max_{\pi\in\Pi(\mu,\nu)}H(\pi,\beta)=\max_{\pi\in\Pi(\mu,\nu)}\inf_{\beta\in\mathcal L^1(\gamma_\sigma)}H(\pi,\beta).$$
--
--   This minimax equality is step (8) of the proof of Theorem 1.
--
--   **Formalization Note.** "max" is stated as attainment of the supremum by some coupling, plus the equality of the extended-real inf–sup and sup–inf. On the page $\gamma,\Gamma$ stand for $\gamma_\sigma,\Gamma_\sigma$.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 11, Proposition 3

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem proposition_3 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) :
    (∀ β : ℝ → ℝ, Integrable β (gam sig) →
      ∃ π ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν,
        H sig L π' β ≤ H sig L π β) ∧
    (∃ π ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν,
      (⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L π' β) ≤
        ⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L π β) ∧
    (⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)),
        ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν, H sig L π β) =
      ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν,
        ⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L π β := by sorry

end MaxSpectralRisk.Duality
