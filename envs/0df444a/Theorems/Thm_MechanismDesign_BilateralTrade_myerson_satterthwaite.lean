-- Prove2me | Theorems.Thm_MechanismDesign_BilateralTrade_myerson_satterthwaite
-- name    : MechanismDesign.BilateralTrade.myerson_satterthwaite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:55:46.316982+00:00
-- url     : https://prove2.me/theorems/c1f1e481-6c10-42ee-a659-112036018b45
-- title:
--   Proposition 3.12 -- Myerson and Satterthwaite (1983)
-- statement:
--   A seller with value $\theta_S$ and a buyer with value $\theta_B$ can trade one indivisible good. The values are independent, $\theta_S$ has a density $f_S > 0$ on $[\underline\theta_S, \overline\theta_S]$ and $\theta_B$ a density $f_B > 0$ on $[\underline\theta_B, \overline\theta_B]$, with $\underline\theta_S < \overline\theta_S$ and $\underline\theta_B < \overline\theta_B$. A first-best trading rule $q^*$ trades whenever $\theta_B > \theta_S$ and never when $\theta_B < \theta_S$; its choice at ties is arbitrary.
--
--   There exists a direct mechanism $(q, t_S, t_B)$ that is Bayesian incentive-compatible, interim individually rational ($U_S(\theta_S) \ge \theta_S$, $U_B(\theta_B) \ge 0$), ex post budget balanced ($t_S(\theta) = t_B(\theta)$ for every $\theta$), and whose trading rule $q$ is first best, if and only if
--
--   $$
--   \underline\theta_B \ge \overline\theta_S \quad\text{or}\quad \underline\theta_S \ge \overline\theta_B .
--   $$
--
--   The two conditions are the trivial cases in which trade is always, respectively never, efficient. In every other case efficient bilateral trade cannot be achieved by a voluntary, budget-balanced trading institution when both parties hold private information.
--
--   **Formalization Note** The existential ranges over all first-best trading rules, so every tie rule is allowed. Budget balance is the ex post equality $t_S = t_B$ on $\Theta$. Mechanisms are required to be well defined (measurable $q, t_S, t_B$ with integrable transfers), the measurability the book omits by convention (Ch. 2 note 2).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.66, Proposition 3.12

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Proposition 3.12 (Myerson and Satterthwaite, 1983), p.66: a well-defined,
incentive-compatible, individually rational and ex post budget balanced direct mechanism whose
trading rule is first best (any tie rule) exists if and only if `θ̲_B ≥ θ̄_S` or `θ̲_S ≥ θ̄_B`. -/
theorem myerson_satterthwaite (E : Environment) :
    (∃ m : DirectMechanism E, m.Admissible ∧ m.ExPostBB ∧ IsFirstBestRule E m.q) ↔
      (E.hiS ≤ E.loB ∨ E.hiB ≤ E.loS) := by sorry

end MechanismDesign.BilateralTrade
