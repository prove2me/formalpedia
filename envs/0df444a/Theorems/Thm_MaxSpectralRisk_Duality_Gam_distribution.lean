-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_Gam_distribution
-- name    : MaxSpectralRisk.Duality.Gam_distribution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:21.891671+00:00
-- url     : https://prove2.me/theorems/2cc0ab2a-08ca-42bb-b8f1-57a1dabd2c45
-- title:
--   §2.2, p. 6 — γσ has distribution function σ, and Γσ is a probability measure with distribution function (1 − u)σ(u) + ∫₀ᵘσ
-- statement:
--   Let $\sigma$ be a bounded, right-continuous spectral function, $\gamma_\sigma$ the measure on $[0,1)$ with distribution function $\sigma$, and $\Gamma_\sigma$ the measure $d\Gamma_\sigma(u)=(1-u)\,d\gamma_\sigma(u)$. Then for every $u\in[0,1)$, $\gamma_\sigma([0,u])=\sigma(u)$; $\Gamma_\sigma$ is a probability measure; and for every $u\in[0,1)$,
--   $$\Gamma_\sigma([0,u])=(1-u)\sigma(u)+\int_0^u\sigma(v)\,dv.$$
--
--   The paper introduces $\Gamma_\sigma$ as the probability measure with this distribution function and records that $d\Gamma_\sigma=(1-u)\,d\gamma_\sigma$ by integration by parts. This milestone checks that the two descriptions agree, so that every later statement about $\Gamma_\sigma$ is about the paper's measure.
--
--   **Formalization Note.** The mission defines $\Gamma_\sigma$ through the density $1-u$; this theorem is the paper's definition, stated as a property. Distribution functions are taken as $\Gamma_\sigma((-\infty,u])$, which equals $\Gamma_\sigma([0,u])$ since $\Gamma_\sigma$ lives on $[0,1)$.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 6, §2.2, display after (2) (definition of γσ, Γσ and dΓσ(u) = (1 − u)dγσ(u)), footnote 4

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem Gam_distribution (sig : SpectralFunction) :
    (∀ u ∈ Set.Ico (0 : ℝ) 1, (gam sig).real (Set.Iic u) = sig u) ∧
    IsProbabilityMeasure (Gam sig) ∧
    ∀ u ∈ Set.Ico (0 : ℝ) 1,
      (Gam sig).real (Set.Iic u) = (1 - u) * sig u + ∫ v in (0 : ℝ)..u, sig v := by sorry

end MaxSpectralRisk.Duality
