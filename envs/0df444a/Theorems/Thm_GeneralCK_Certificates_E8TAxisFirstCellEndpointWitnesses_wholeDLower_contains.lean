-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_wholeDLower_contains
-- name    : GeneralCK.Certificates.E8TAxisFirstCellEndpointWitnesses.wholeDLower_contains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:29:52.948677+00:00
-- url     : https://prove2.me/theorems/f4875b4a-c4e1-421d-8371-eb4e6527f852
-- title:
--   E8 whole-cell D: checked lower endpoint enclosure
-- statement:
--   For the whole-cell D padded inverse bracket, let $a_0$ be its lower endpoint and let $J=[L/2^{160},U/2^{160}]$ be the saved endpoint output interval. Then $$Y(a_0)\in J.$$ Here $Y$ is the stable scalar slope map: with $z=e^{-2a}$, $r=(1-z)/(1+z)$, $q=4z/(1+z)^2$, $\ell=a+\log(1+z)$, and $h=\log(1+z)+2az/(1+z)$, $Y(a)=\frac{2}{\log 2}\left(a+\frac{rh}{q\ell}\right)$. The bracket and integer bounds L and U are the named exact constants in the formal statement. The enclosure is one of the two endpoint facts used to prove inverse-slope coverage by continuity.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisFirstCellEndpointWitnesses.lean#L426-L431

import Definitions.Def_GeneralCK_E8_first_cell_inputs
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_E8TAxisFirstCellEndpointWitnesses_data

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisFirstCellEndpointWitnesses
open Set GeneralCK.Certificates.DyadicInterval GeneralCK.Certificates.E8TAxisStableInterval GeneralCK.Certificates.E8TAxisStableScalar
open GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage GeneralCK.Certificates.E8TAxisOneCellGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem GeneralCK.Certificates.E8TAxisFirstCellEndpointWitnesses.wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisFirstCellPaddedInputs.wholeDInput.alpha)) := by sorry
