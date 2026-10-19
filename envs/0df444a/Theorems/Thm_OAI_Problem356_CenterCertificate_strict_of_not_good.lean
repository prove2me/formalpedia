-- Prove2me | Theorems.Thm_OAI_Problem356_CenterCertificate_strict_of_not_good
-- name    : OAI.Problem356.CenterCertificate.strict_of_not_good
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:59:17.927251+00:00
-- url     : https://prove2.me/theorems/f62eea12-804f-4157-8106-d00f0bbe2439
-- title:
--   Strict gap of the center certificate at bad types
-- statement:
--   Let the five centers be $P_0=0$, $P_{1,2}=\pm e_1$, $P_{3,4}=\pm e_2$ in $\mathbb{R}^3$, with potential $\frac52$ at $P_0$ and $0$ elsewhere. If a triple of indices $(i,j,k)$ is not good, i.e. $\{i,j,k\}$ is neither $\{0,1,2\}$ nor $\{0,3,4\}$, then
--   $$
--   v_i+v_j+v_k<c(P_i,P_j,P_k) .
--   $$
--
--   Only the two good families can be in contact with the certificate. Every other component type has a strict gap, which survives small perturbations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CenterCertificate.lean#L95-L111

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

open OAI OAI.Problem356 OAI.Problem356.CenterCertificate
open scoped ENNReal

theorem OAI.Problem356.CenterCertificate.strict_of_not_good (i j k : Fin 5) (h : ¬ Good i j k) :
    potential i + potential j + potential k <
      coulombCost (point i, (point j, point k)) := by sorry
