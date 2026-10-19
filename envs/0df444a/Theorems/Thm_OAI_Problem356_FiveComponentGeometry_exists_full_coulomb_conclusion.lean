-- Prove2me | Theorems.Thm_OAI_Problem356_FiveComponentGeometry_exists_full_coulomb_conclusion
-- name    : OAI.Problem356.FiveComponentGeometry.exists_full_coulomb_conclusion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:56:08.647704+00:00
-- url     : https://prove2.me/theorems/03b164f6-7e96-49f7-8f67-96325e3c3c0d
-- title:
--   Existence of a density with the full Coulomb conclusion
-- statement:
--   A density $\rho$ has the full Coulomb conclusion if it is a smooth compact probability density whose measure $\mu=\rho\,dx$ has finite, attained Kantorovich value, admits no Monge optimizer, has Monge value equal to the Kantorovich value, and is approximated within any $\varepsilon>0$ by pairs of $\mu$-preserving maps of finite graph cost. Then there is a density $\rho$ on $\mathbb{R}^3$ with
--   $$
--   \rho\text{ has the full Coulomb conclusion} .
--   $$
--
--   This is the unconditional witness assembled from the two actual Coulomb charts and their global certificate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/ActualGeometryConclusion.lean#L186-L206

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterAxis

open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace
open LocalGeometry CenterCertificate

theorem OAI.Problem356.FiveComponentGeometry.exists_full_coulomb_conclusion :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by sorry
