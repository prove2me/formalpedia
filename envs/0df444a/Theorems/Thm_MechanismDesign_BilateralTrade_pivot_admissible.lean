-- Prove2me | Theorems.Thm_MechanismDesign_BilateralTrade_pivot_admissible
-- name    : MechanismDesign.BilateralTrade.pivot_admissible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:53:59.275995+00:00
-- url     : https://prove2.me/theorems/fa64fef6-adf2-451f-a2fd-5c9c6b2ab046
-- title:
--   Lemma 3.9 -- the pivot mechanism is incentive-compatible and individually rational
-- statement:
--   Consider the bilateral trade environment: the seller's value $\theta_S$ has a density $f_S > 0$ on $[\underline\theta_S, \overline\theta_S]$, the buyer's value $\theta_B$ an independent density $f_B > 0$ on $[\underline\theta_B, \overline\theta_B]$. Let $q^*$ be a measurable first-best trading rule: $q^*(\theta) = 1$ when $\theta_B > \theta_S$, $q^*(\theta) = 0$ when $\theta_B < \theta_S$, and either value at ties. The pivot mechanism uses $q^*$ and the transfers
--
--   $$
--   t_S(\theta) = q^*(\overline\theta_S, \theta_B)\overline\theta_S + \big(q^*(\theta) - q^*(\overline\theta_S,\theta_B)\big)\theta_B, \qquad t_B(\theta) = q^*(\theta_S, \underline\theta_B)\underline\theta_B + \big(q^*(\theta) - q^*(\theta_S,\underline\theta_B)\big)\theta_S .
--   $$
--
--   Then the pivot mechanism is Bayesian incentive-compatible and interim individually rational: $U_S(\theta_S) \ge \theta_S$ and $U_B(\theta_B) \ge 0$ for all types.
--
--   This is the first step of the proof of the Myerson–Satterthwaite theorem: it exhibits one incentive-compatible, individually rational mechanism implementing efficient trade, against which all others are compared.
--
--   **Formalization Note** The conclusion is `Admissible`, which also records that the pivot mechanism is well defined (measurable, integrable transfers); this is why the measurability of $q^*$ is assumed.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.67, Lemma 3.9 (with Definition 3.10, p.66)

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Lemma 3.9 (p.67): the pivot mechanism (Definition 3.10) is incentive-compatible and
individually rational. Stated for every measurable first-best trading rule `q*` (any tie rule);
the conclusion also records that the pivot mechanism is well defined (measurable, integrable). -/
theorem pivot_admissible (E : Environment) (q : ℝ × ℝ → ℝ) (hq : IsFirstBestRule E q)
    (hqm : Measurable q) :
    (pivot E q hq).Admissible := by sorry

end MechanismDesign.BilateralTrade
