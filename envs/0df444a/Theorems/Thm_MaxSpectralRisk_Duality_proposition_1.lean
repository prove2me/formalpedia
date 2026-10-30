-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_proposition_1
-- name    : MaxSpectralRisk.Duality.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:26.119082+00:00
-- url     : https://prove2.me/theorems/07347080-077b-485b-8f38-fefb3b2bb084
-- title:
--   Proposition 1, p. 8 — weak duality: D_σ(µ, ν) ≥ V_σ(µ, ν)
-- statement:
--   Throughout, $\mathcal X$ and $\mathcal Y$ are Polish spaces with their Borel $\sigma$-algebras, $\mu$ and $\nu$ are Borel probability measures on them, $\Pi(\mu,\nu)$ is the set of couplings, $\sigma$ is a bounded, right-continuous spectral function (A.4), and $L:\mathcal X\times\mathcal Y\to\mathbb R$ is the loss. Under A.1–A.3,
--   $$D_\sigma(\mu,\nu)\ \ge\ V_\sigma(\mu,\nu).$$
--
--   Every dual feasible triple $(\beta,\varphi,\psi)$ bounds every spectral risk $R_{\pi,\sigma}(L)$ over couplings from above. This is the easy half of Theorem 1.
--
--   **Formalization Note.** Both sides take values in the extended reals. The page states Proposition 1 without hypotheses; it sits under the assumptions A.1–A.4 of p. 7, and its proof uses Lemma 1, so A.1–A.3 are hypotheses here (A.4 is part of the spectral function).
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 8, Proposition 1

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem proposition_1 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) :
    V sig L μ ν ≤ D sig L μ ν := by sorry

end MaxSpectralRisk.Duality
