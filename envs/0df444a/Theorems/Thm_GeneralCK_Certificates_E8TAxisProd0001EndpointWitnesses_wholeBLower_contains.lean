-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_wholeBLower_contains
-- name    : GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses.wholeBLower_contains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T02:24:35.219303+00:00
-- url     : https://prove2.me/theorems/f26bdaa3-1570-4a78-be08-b511525a6d85
-- title:
--   E8 production cell 0001 whole-cell B: lower endpoint enclosure
-- statement:
--   For the lower endpoint a of the named padded inverse bracket, the saved exact dyadic interval encloses Y(a). Here $Y(a)=\frac{2}{\log 2}(a+rh/(q\ell))$, where $z=e^{-2a}$, $r=(1-z)/(1+z)$, $q=4z/(1+z)^2$, $\ell=a+\log(1+z)$ and $h=\log(1+z)+2az/(1+z)$.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_E8_Prod0001_inputs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_E8_Prod0001_endpoint_data

open GeneralCK GeneralCK.Certificates
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0001Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses

theorem GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses.wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisProd0001PaddedInputs.wholeBInput.alpha)) := by sorry
