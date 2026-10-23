-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_theorem_1
-- name    : MaxSpectralRisk.Duality.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:26.984863+00:00
-- url     : https://prove2.me/theorems/36cbe29c-e783-4d50-ab06-dcd661ef035b
-- title:
--   Theorem 1, p. 11 — strong duality: the Maximum Spectral Measure V_σ(µ, ν) equals the dual value D_σ(µ, ν) under A.1–A.4
-- statement:
--   Throughout, $\mathcal X$ and $\mathcal Y$ are Polish spaces with their Borel $\sigma$-algebras, $\mu$ and $\nu$ are Borel probability measures on them, $\Pi(\mu,\nu)$ is the set of couplings, $\sigma$ is a bounded, right-continuous spectral function (A.4), and $L:\mathcal X\times\mathcal Y\to\mathbb R$ is the loss. Assume A.1–A.4. Then the Maximum Spectral Measure equals its dual value:
--   $$V_\sigma(\mu,\nu)=\sup_{\pi\in\Pi(\mu,\nu)}R_{\pi,\sigma}(L)\;=\;\inf_{\beta\in\mathcal L^1(\gamma_\sigma),\,(\varphi,\psi)\in\Phi_{C^\beta}}\int_0^1\beta\,d\Gamma_\sigma+\int\varphi\,d\mu+\int\psi\,d\nu=D_\sigma(\mu,\nu).$$
--
--   The worst-case spectral risk of $L(X,Y)$ over all dependence structures with given marginals is thus the value of a dual problem over a threshold function $\beta$ and a pair of Kantorovich potentials for the cost $C^\beta$. For $\sigma\equiv1$ it reduces to Kantorovich duality, and for Expected Shortfall to a one-parameter family of transport problems.
--
--   **Formalization Note.** $V_\sigma$ and $D_\sigma$ are extended-real supremum and infimum. A.4 is built into the encoding of the spectral function, and "for $\mu$-a.e. $x$ and $\nu$-a.e. $y$" in A.2, A.3 and $\Phi_{C^\beta}$ is read as "off a null rectangle". Attainment of the primal supremum is not part of the statement.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 11, Theorem 1

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem theorem_1 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) :
    V sig L μ ν = D sig L μ ν := by sorry

end MaxSpectralRisk.Duality
