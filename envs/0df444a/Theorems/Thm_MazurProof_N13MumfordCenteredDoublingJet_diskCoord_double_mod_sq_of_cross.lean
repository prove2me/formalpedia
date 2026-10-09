-- Prove2me | Theorems.Thm_MazurProof_N13MumfordCenteredDoublingJet_diskCoord_double_mod_sq_of_cross
-- name    : MazurProof.N13MumfordCenteredDoublingJet.diskCoord_double_mod_sq_of_cross
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T03:51:48.879983+00:00
-- url     : https://prove2.me/theorems/0804b129-98c2-4fc5-8c67-853ab3d2007a
-- title:
--   Mazur 13 port: diskCoord_double_mod_sq_of_cross
-- statement:
--   The two odd cross coefficients determine the actual doubled disk coordinates modulo the square of the original moving coordinate ideal. The constant and linear coefficients first put both coordinates of `Q` in the ideal of `P`; cancellation of the unit `Q.x₁` is the only local-ring step. The remaining difference between polynomial and disk coordinates is a product of two first-order coordinates, hence quadratic.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordCenteredDoublingJet.lean#L247

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13MumfordCenteredDoublingJet
open Polynomial
attribute [local instance] MazurProof.N13MumfordCenteredDoublingJet.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13MumfordCenteredDoublingJet.diskCoord_double_mod_sq_of_cross (P Q : DiskPair) (h₁ : (P.u ^ 2 - N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 1 ∈ N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P * N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P) (h₃ : (P.u ^ 2 - N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 3 ∈ N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P * N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P) (i : Fin 2) : N13TwoAdicAbelChartData.DiskPair.coord Q i - (N13TwoAdicAbelChartData.DiskPair.coord P i + N13TwoAdicAbelChartData.DiskPair.coord P i) ∈ N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P * N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P := by sorry
