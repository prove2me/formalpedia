-- Prove2me | Theorems.Thm_GEPPGrowth_Main_covariance_process_laws
-- name    : GEPPGrowth.Main.covariance_process_laws
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:37:51.33354+00:00
-- url     : https://prove2.me/theorems/d6f01c9b-6842-43bf-8036-56d38ee23e6b
-- title:
--   Covariance kernel normalization, trajectories, and actual GEPP law
-- statement:
--   Let $n$ be the initial dimension and let $K_D$ be the explicit fresh-Gaussian covariance transition of the definition layer. For every dimension $D$, state $S$, and measurable state event $E$, the function $S\mapsto K_D(S,E)$ is measurable and $K_D(S,\cdot)$ is a probability measure. Every finite trajectory law is a probability measure, and its last-state marginal is $\mu_{n,t}$:
--
--   $$\operatorname{Law}(\Sigma_t)=\mu_{n,t}.$$
--
--   For every $0\le t\le n$, the covariance trajectory computed from actual GEPP on the full Gaussian input has this same finite trajectory law. Given the first $t$ original columns, the residual columns have the independent centered Gaussian law with this actual covariance, in the measurable-history integral sense defined above.
--
--   This makes the covariance process an explicit probabilistic construction connected to the algorithm, rather than a sequence postulated to have favorable properties.
--
--   Differences from the source:
--   - encoding: successive covariance updates and conditional Gaussian residual columns → explicit transition measures, finite trajectory marginals, and measurable-history integral identities; reason: spells out the probability construction and its iteration without adding hypotheses
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), §3 and Proposition 3.1, printed pp.6–7, PDF pp.7–8 (iteration and well-posedness obligations)

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- §3: explicit transition distributions, their finite trajectories, and the connection to actual GEPP. These are conclusions, not fields assumed of a process. -/
theorem covariance_process_laws (n : ℕ) :
    (∀ d, ∀ E : Set CovState, MeasurableSet E → Measurable (fun S => covStep d S E)) ∧
    (∀ d S, IsProbabilityMeasure (covStep d S)) ∧
    (∀ t, IsProbabilityMeasure (covLaw n t) ∧ IsProbabilityMeasure (trajectoryLaw n t) ∧
      (trajectoryLaw n t).map (fun h => h (Fin.last t)) = covLaw n t) ∧
    (∀ t (ht : t ≤ n), HasResidualLaw n t ht ∧
      (GaussianMatrix.gaussianMatrix n n).map (fun A => fun j : Fin (t+1) => actualCov A j.val) =
        trajectoryLaw n t) := by sorry

end GEPPGrowth.Main
