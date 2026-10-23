-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_lemma_1
-- name    : MaxSpectralRisk.Duality.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:17.001204+00:00
-- url     : https://prove2.me/theorems/868fb5da-4835-460e-9c42-55d1212c0397
-- title:
--   Lemma 1, p. 8 — for β ∈ L¹(γσ), C^β is upper semicontinuous, finite-valued and 0 ≤ C^β ≤ A^β(x) + B^β(y)
-- statement:
--   Assume A.1–A.4 and let $\beta\in\mathcal L^1(\gamma_\sigma)$. Then:
--
--   1. $(x,y)\mapsto C^\beta(x,y)=\int_0^1\max(L(x,y)-\beta(u),0)\,d\gamma_\sigma(u)$ is upper semicontinuous;
--   2. $C^\beta$ is finite-valued: for every $(x,y)$ the integrand $u\mapsto\max(L(x,y)-\beta(u),0)$ is $\gamma_\sigma$-integrable;
--   3. $0\le C^\beta(x,y)$ for all $(x,y)$;
--   4. there are $A^\beta\in\mathcal L^1(\mu)$ and $B^\beta\in\mathcal L^1(\nu)$ with
--   $$C^\beta(x,y)\le A^\beta(x)+B^\beta(y)\quad\text{for $\mu$-a.e. }x\text{ and $\nu$-a.e. }y.$$
--
--   The lemma makes the dual feasible set nonempty and puts the cost $C^\beta$ in the setting of Kantorovich duality.
--
--   **Formalization Note.** The paper prints the upper bound without a qualifier; A.2–A.3 give it off a null rectangle $N\times\mathcal Y\cup\mathcal X\times N'$, which is how it is stated here. Hypotheses A.1–A.3 are those of the section (p. 7).
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 8, Lemma 1

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem lemma_1 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) (β : ℝ → ℝ) (hβ : Integrable β (gam sig)) :
    UpperSemicontinuous (fun p : X × Y => Cbeta sig L β p.1 p.2) ∧
    (∀ x y, Integrable (fun u => max (L (x, y) - β u) 0) (gam sig)) ∧
    (∀ x y, 0 ≤ Cbeta sig L β x y) ∧
    ∃ (Aβ : X → ℝ) (Bβ : Y → ℝ), Integrable Aβ μ ∧ Integrable Bβ ν ∧
      AERect μ ν (fun x y => Cbeta sig L β x y ≤ Aβ x + Bβ y) := by sorry

end MaxSpectralRisk.Duality
