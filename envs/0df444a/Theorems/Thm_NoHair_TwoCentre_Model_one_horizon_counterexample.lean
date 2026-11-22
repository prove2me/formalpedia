-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Model_one_horizon_counterexample
-- name    : NoHair.TwoCentre.Model.one_horizon_counterexample
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T21:51:00.645623+00:00
-- url     : https://prove2.me/theorems/84975594-a830-42db-a289-c13d23e1c01b
-- title:
--   A two-centre static electrovacuum counterexample with one included future horizon
-- statement:
--   For the explicitly specified manifold, metric, Faraday field, time orientation, and stationary flow, there exists an asymptotically flat end satisfying every hypothesis of the Israel electrovacuum milestone, whose domain of outer communications fails the Reissner–Nordström conclusion for every admissible mass and charge. The construction extends the left future horizon of the two-centre Majumdar–Papapetrou exterior and leaves the other throat unextended. This existential theorem gives a concrete counterexample to the positive uniqueness statement. Its open child problems record which parts of the construction still require formal proof. [Positive milestone](https://prove2.me/theorems/ae80f2c5-e7b6-4f5e-ab99-ed248fa30fca)
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696. M. Sánchez, On the geometry of static spacetimes, Theorem 3.1, https://arxiv.org/abs/math/0406332. P. T. Chruściel and P. Tod, compact-interior hypothesis in Theorem 1.1, https://arxiv.org/abs/gr-qc/0512043.

import Definitions.Def_NoHair_TwoCentreBlackHole
import Definitions.Def_NoHair_TwoCentreIsotropic

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model Set
open scoped ContDiff Manifold

theorem NoHair.TwoCentre.Model.one_horizon_counterexample :
    ∃ E : AsymptoticallyFlatEnd metric faraday flow,
      IsStationaryBlackHole metric faraday orientation flow E ∧
      IsStaticOn metric flow (domainOfOuterCommunications metric orientation E.region) ∧
      ¬ ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧
        IsKerrNewmanDOC metric faraday (domainOfOuterCommunications metric orientation E.region) m 0 e := by
  sorry
