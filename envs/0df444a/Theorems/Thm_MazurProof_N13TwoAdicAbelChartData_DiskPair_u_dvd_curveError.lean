-- Prove2me | Theorems.Thm_MazurProof_N13TwoAdicAbelChartData_DiskPair_u_dvd_curveError
-- name    : MazurProof.N13TwoAdicAbelChartData.DiskPair.u_dvd_curveError
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:45:17.068372+00:00
-- url     : https://prove2.me/theorems/ba891bf9-cd5b-459f-b962-eb5adcbb4927
-- title:
--   Mazur 13 port: u_dvd_curveError
-- statement:
--   Supporting lemma `u_dvd_curveError` (namespace `MazurProof.N13TwoAdicAbelChartData.DiskPair`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13TwoAdicAbelChartData.lean#L224

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13TwoAdicAbelChartData MazurProof.N13TwoAdicAbelChartData.DiskPair
open Polynomial
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13TwoAdicAbelChartData.DiskPair.u_dvd_curveError : P.u ∣ P.curveError := by sorry
