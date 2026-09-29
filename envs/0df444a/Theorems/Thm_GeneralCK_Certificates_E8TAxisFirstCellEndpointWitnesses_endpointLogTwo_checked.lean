-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_endpointLogTwo_checked
-- name    : GeneralCK.Certificates.E8TAxisFirstCellEndpointWitnesses.endpointLogTwo_checked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:28:47.963772+00:00
-- url     : https://prove2.me/theorems/2c3db09a-ecaa-4b77-bba3-02c8f77f86c3
-- title:
--   Checked logarithm-of-two interval for E8 endpoint witnesses
-- statement:
--   At dyadic precision $p=160$, the fast logarithm checker accepts the saved witness for the source interval $J$ named endpointLogTwo: $$\operatorname{logBoxCheck}(\operatorname{ofInt}(160,2),J,w)=\mathrm{true}.$$ Here $w$ is the saved FastLogBoxWitness and ofInt encodes the exact integer input at scale $2^{160}$. This finite kernel check supplies the logarithm-of-two premise shared by all sixteen endpoint enclosures.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisFirstCellEndpointWitnesses.lean#L25-L26

import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8TAxisFirstCellEndpointWitnesses_data

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisFirstCellEndpointWitnesses
open Set GeneralCK.Certificates.DyadicInterval GeneralCK.Certificates.E8TAxisStableInterval GeneralCK.Certificates.E8TAxisStableScalar
open GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage GeneralCK.Certificates.E8TAxisOneCellGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem GeneralCK.Certificates.E8TAxisFirstCellEndpointWitnesses.endpointLogTwo_checked :
    logBoxCheck (ofInt precision 2) endpointLogTwo fastLogWitness = true := by sorry
