-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_es_representation
-- name    : MaxSpectralRisk.Duality.es_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:21.107078+00:00
-- url     : https://prove2.me/theorems/20300562-78fe-45e3-abcd-74a2357290c6
-- title:
--   §2.2, p. 6 — R_{π,σ}(L) = ∫₀¹ ES_{u,π}(L) dΓσ(u)
-- statement:
--   Let $\sigma$ be a bounded, right-continuous spectral function, $\pi$ a probability measure on $\mathcal W$ and $L\in\mathcal L^1(\pi)$. Then $u\mapsto\mathrm{ES}_{u,\pi}(L)$ is $\Gamma_\sigma$-integrable and
--   $$R_{\pi,\sigma}(L)=\int_0^1\mathrm{ES}_{u,\pi}(L)\,d\Gamma_\sigma(u).$$
--
--   A spectral risk measure is thus an average of Expected Shortfalls as well as of Values-at-Risk. Combined with (2) it is the first line of the informal derivation of the dual on p. 7. The atom $\Gamma_\sigma(\{0\})=z_0=\sigma(0)$ contributes $z_0\,\mathbb E_\pi[L]$.
--
--   **Formalization Note.** Integrability is asserted, so the Bochner integral on the right is never Lean's default value $0$. $L$ is measurable and $\pi$-integrable.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 6, §2.2, display after (2): Rπ,σ(L) = ∫₀¹ ES_{u,π}(L) dΓσ(u)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem es_representation {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (sig : SpectralFunction) (π : Measure (X × Y)) [IsProbabilityMeasure π] (L : X × Y → ℝ)
    (hLm : Measurable L) (hL : Integrable L π) :
    Integrable (fun u => ES u π L) (Gam sig) ∧
    specRisk sig π L = ∫ u, ES u π L ∂(Gam sig) := by sorry

end MaxSpectralRisk.Duality
