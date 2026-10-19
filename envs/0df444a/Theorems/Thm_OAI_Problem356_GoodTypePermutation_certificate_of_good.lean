-- Prove2me | Theorems.Thm_OAI_Problem356_GoodTypePermutation_certificate_of_good
-- name    : OAI.Problem356.GoodTypePermutation.certificate_of_good
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:34:15.389053+00:00
-- url     : https://prove2.me/theorems/1048dc66-94dd-43f9-be0e-bfff668deff5
-- title:
--   Two canonical orders certify every good component type
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. Let $U_0,\dots,U_4$ be sets with potentials $v_i$, and $\mathrm{Contact}$ a predicate on triples invariant under permuting the three points. Suppose the local type certificate holds for the types $(0,1,2)$ and $(0,3,4)$: $v_i(x)+v_j(y)+v_k(z)\le c(x,y,z)$ on $U_i\times U_j\times U_k$, and equality implies contact. Then it holds for every good type $(i,j,k)$, i.e. whenever
--   $$
--   \{i,j,k\}=\{0,1,2\}\quad\text{or}\quad\{i,j,k\}=\{0,3,4\} .
--   $$
--
--   Both the potential sum and the Coulomb cost are symmetric in the three points, so one ordering per family suffices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/GoodTypePermutation.lean#L46-L66

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

open OAI OAI.Problem356 OAI.Problem356.GoodTypePermutation
open scoped ENNReal
variable {U : Fin 5 → Set E3} {v : Fin 5 → E3 → ℝ}
  {Contact : Triple → Prop}

theorem OAI.Problem356.GoodTypePermutation.certificate_of_good
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c)))
    (h012 : LocalTypeCertificate U v Contact 0 1 2)
    (h034 : LocalTypeCertificate U v Contact 0 3 4)
    (i j k : Fin 5) (hgood : CenterCertificate.Good i j k) :
    LocalTypeCertificate U v Contact i j k := by sorry
