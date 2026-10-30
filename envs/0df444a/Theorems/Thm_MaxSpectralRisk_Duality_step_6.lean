-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_step_6
-- name    : MaxSpectralRisk.Duality.step_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:21.049971+00:00
-- url     : https://prove2.me/theorems/6b325aad-e7c2-4ce1-9306-b33098594820
-- title:
--   (6), proof of Theorem 1, p. 11 — inf_{(φ,ψ)∈Φ_{C^β}} ∫φ dµ + ∫ψ dν = max_{π∈Π(µ,ν)} E_π[C^β] for β ∈ L¹(γσ)
-- statement:
--   Throughout, $\mathcal X$ and $\mathcal Y$ are Polish spaces with their Borel $\sigma$-algebras, $\mu$ and $\nu$ are Borel probability measures on them, $\Pi(\mu,\nu)$ is the set of couplings, $\sigma$ is a bounded, right-continuous spectral function (A.4), and $L:\mathcal X\times\mathcal Y\to\mathbb R$ is the loss. Assume A.1–A.3 and let $\beta\in\mathcal L^1(\gamma_\sigma)$, with $C^\beta$ as in (5). Then
--   $$\inf_{(\varphi,\psi)\in\Phi_{C^\beta}}\int\varphi\,d\mu+\int\psi\,d\nu=\max_{\pi\in\Pi(\mu,\nu)}\mathbb E_\pi[C^\beta(X,Y)],$$
--   and the maximum on the right is attained by some coupling.
--
--   This is the Kantorovich duality for the upper semicontinuous cost $C^\beta$, which the paper cites from Villani (2008, Theorem 5.10). It is equality (6) of the proof of Theorem 1; taking $\int\beta\,d\Gamma_\sigma$ plus each side and the infimum over $\beta$ gives the display (6).
--
--   **Formalization Note.** The milestone states the inner equality for each fixed $\beta$, which implies the paper's display. The dual constraint $\varphi(x)+\psi(y)\ge C^\beta(x,y)$ holds off a null rectangle, as in $\Phi_{C^\beta}$. Values are in the extended reals.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 11, equality (6) in the proof of Theorem 1

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem step_6 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) (β : ℝ → ℝ) (hβ : Integrable β (gam sig)) :
    (⨅ φψ ∈ PhiC sig L μ ν β, (((∫ x, φψ.1 x ∂μ) + ∫ y, φψ.2 y ∂ν : ℝ) : EReal)) =
      ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν, ((∫ p, Cbeta sig L β p.1 p.2 ∂π : ℝ) : EReal) ∧
    ∃ π ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν,
      ∫ p, Cbeta sig L β p.1 p.2 ∂π' ≤ ∫ p, Cbeta sig L β p.1 p.2 ∂π := by sorry

end MaxSpectralRisk.Duality
