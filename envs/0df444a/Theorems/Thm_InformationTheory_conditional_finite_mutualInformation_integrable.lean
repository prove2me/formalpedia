-- Prove2me | Theorems.Thm_InformationTheory_conditional_finite_mutualInformation_integrable
-- name    : InformationTheory.conditional_finite_mutualInformation_integrable
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T03:15:49.111053+00:00
-- url     : https://prove2.me/theorems/f1900ec7-d3c4-4767-8e37-920ec9d90a92
-- title:
--   Integrability of conditional mutual information with a finite coordinate
-- statement:
--   Let $\mu$ be a probability measure, let $H$ and $Y$ be standard Borel spaces, and let $A$ take values in the finite set $[k]$. For measurable random variables $H(\omega)$, $Y(\omega)$, and $A(\omega)$, write $\mu_h^{A,Y}$, $\mu_h^A$, and $\mu_h^Y$ for their regular conditional laws given $H=h$. Then the conditional mutual-information density is integrable:
--
--   $$
--   h\longmapsto D\!\left(\mu_h^{A,Y}\,\middle\|\,\mu_h^A\otimes\mu_h^Y\right)\in L^1(\mu_H).
--   $$
--
--   This finite-coordinate result supplies the measurability and integrability needed to use conditional information gains in information-ratio arguments.
--
--   **Formalization Note** The proof represents the density as an integral of categorical posterior divergences and bounds it by the entropy of a distribution on $[k]$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 / free PDF p. 479; measure-theoretic finite-posterior integrability bridge used to formalize its conditional mutual information.

import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory ProbabilityTheory InformationTheory

namespace InformationTheory

/-- Conditional mutual information is integrable when one coordinate takes
values in a finite type. -/
theorem conditional_finite_mutualInformation_integrable
    {Omega H Y : Type} {mOmega : MeasurableSpace Omega}
    {mH : MeasurableSpace H} {mY : MeasurableSpace Y}
    [StandardBorelSpace H] [StandardBorelSpace Y] [Nonempty Y]
    {k : ℕ} [NeZero k]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (hist : Omega → H) (obs : Omega → Y) (act : Omega → Fin k)
    (hhist : Measurable hist) (hobs : Measurable obs) (hact : Measurable act) :
    Integrable
      (fun h ↦ (klDiv (condDistrib (fun w ↦ (act w, obs w)) hist mu h)
        ((condDistrib act hist mu h).prod (condDistrib obs hist mu h))).toReal)
      (mu.map hist) := by
  sorry

end InformationTheory
