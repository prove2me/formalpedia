-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_lemma_3_2
-- name    : LogGammaPolymer.Variance.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:57.29435+00:00
-- url     : https://prove2.me/theorems/8bb90b06-92d8-40a2-8cd0-563d0329e568
-- title:
--   Lemma 3.2 — gamma reversibility: (U′, V′, Y′) ≗ (U, V, Y) iff the inverse-gamma laws (3.6)
-- statement:
--   Let $U,V,Y$ be independent positive random variables and set
--   $$U'=Y(1+UV^{-1}),\qquad V'=Y(1+VU^{-1}),\qquad Y'=(U^{-1}+V^{-1})^{-1}\qquad(3.5).$$
--   Assume that $U$ is not almost surely constant. Then the triple $(U',V',Y')$ has the same distribution as $(U,V,Y)$ if and only if there exist parameters $0<\theta<\mu$ and $r>0$ such that
--   $$U^{-1}\sim\mathrm{Gamma}(\theta,r),\qquad V^{-1}\sim\mathrm{Gamma}(\mu-\theta,r),\qquad Y^{-1}\sim\mathrm{Gamma}(\mu,r)\qquad(3.6).$$
--
--   This is the one-step version of the Burke property: one application of the recursion (3.2) at a corner of the lattice preserves the joint law of the weights exactly when they are reciprocals of gamma variables with a common rate.
--
--   **Formalization Note** The printed lemma has no non-degeneracy hypothesis, and its "only if" direction is false without one: the constants $U=V=1$, $Y=1/2$ are independent and positive and give $(U',V',Y')=(1,1,1/2)$. The hypothesis "$U$ is not a.s. constant" is added. It costs nothing for the "if" direction, since a gamma-distributed $U^{-1}$ is never constant, so this statement is equivalent to the printed "if" plus the corrected "only if". Positivity is required at every sample point.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Lemma 3.2, (3.5)–(3.6), pp. 11–12

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem lemma_3_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (U V Y : Ω → ℝ) (hU : Measurable U) (hV : Measurable V) (hY : Measurable Y)
    (hUpos : ∀ ω, 0 < U ω) (hVpos : ∀ ω, 0 < V ω) (hYpos : ∀ ω, 0 < Y ω)
    (hind : iIndepFun (fun i : Fin 3 => ![U, V, Y] i) P)
    (hnd : ¬ ∃ c : ℝ, U =ᵐ[P] fun _ => c) :
    P.map (fun ω => (Y ω * (1 + U ω / V ω), Y ω * (1 + V ω / U ω), ((U ω)⁻¹ + (V ω)⁻¹)⁻¹))
        = P.map (fun ω => (U ω, V ω, Y ω)) ↔
      ∃ θ μ r : ℝ, 0 < θ ∧ θ < μ ∧ 0 < r ∧
        P.map (fun ω => (U ω)⁻¹) = gammaMeasure θ r ∧
        P.map (fun ω => (V ω)⁻¹) = gammaMeasure (μ - θ) r ∧
        P.map (fun ω => (Y ω)⁻¹) = gammaMeasure μ r := by sorry

end LogGammaPolymer.Variance
