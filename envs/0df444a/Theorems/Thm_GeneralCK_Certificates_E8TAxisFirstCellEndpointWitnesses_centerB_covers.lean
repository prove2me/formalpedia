-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellEndpointWitnesses_centerB_covers
-- name    : GeneralCK.Certificates.E8TAxisFirstCellEndpointWitnesses.centerB_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:28:12.315362+00:00
-- url     : https://prove2.me/theorems/3c108b2f-409f-4bb3-99a9-879c5682aa34
-- title:
--   E8 center B: inverse-slope coverage
-- statement:
--   Let $s_c=57/800$ and $t_c=3/200$. For the center B padded inverse bracket $I$, $$\exists a\in I,\quad a>0\quad\text{and}\quad Y(a)=2s_c+t_c.$$ Here $Y$ is the stable scalar slope map: with $z=e^{-2a}$, $r=(1-z)/(1+z)$, $q=4z/(1+z)^2$, $\ell=a+\log(1+z)$, and $h=\log(1+z)+2az/(1+z)$, $Y(a)=\frac{2}{\log 2}\left(a+\frac{rh}{q\ell}\right)$. The interval I is the corresponding exact padded alpha interval named in the formal statement. This semantic interface supplies the inverse parameters needed by the first-cell stable Taylor graph; numerical endpoint certificates stay inside its proof dependencies.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisFirstCellEndpointWitnesses.lean#L481-L484

import Definitions.Def_GeneralCK_E8_first_cell_inputs
import Definitions.Def_GeneralCK_E8_semantic_core

open GeneralCK GeneralCK.Certificates
open Set GeneralCK.Certificates.DyadicInterval GeneralCK.Certificates.E8TAxisStableInterval GeneralCK.Certificates.E8TAxisStableScalar
open GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage GeneralCK.Certificates.E8TAxisOneCellGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem GeneralCK.Certificates.E8TAxisFirstCellEndpointWitnesses.centerB_covers :
    ∃ a : ℝ, E8TAxisFirstCellPaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = (2 * centerS + centerT) := by sorry
