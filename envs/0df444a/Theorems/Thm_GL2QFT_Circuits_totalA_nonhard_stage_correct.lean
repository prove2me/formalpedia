-- Prove2me | Theorems.Thm_GL2QFT_Circuits_totalA_nonhard_stage_correct
-- name    : GL2QFT.Circuits.totalA_nonhard_stage_correct
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:01:44.130363+00:00
-- url     : https://prove2.me/theorems/dc0b99ea-d5dd-4c9a-a531-73d709c0d467
-- title:
--   The non-hard total A-block equals its routing and closed-form local stages
-- statement:
--   For $q>2$, restriction of the total A-matrix to the non-hard source and output registers factors as $A_{\mathrm{nonhard}}=FLP$, where $P$ initializes the clean two-level register, $L$ is the coherent direct sum of the closed-form one- and two-dimensional gates, and $F$ routes the result to the output irrep labels. Moreover $P^\dagger P=I$ and $L^\dagger L=I$. Entrywise, the factorization is precisely equations (128)–(139); the second columns of the local gates are irrelevant on the initialized register.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, arXiv:2608.28573, §6.4.4, equations (128)–(139), pp.45–46 (PDF pp.46–47).

import Definitions.Def_GL2QFT_Circuits_NonHardStages

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

theorem GL2QFT.Circuits.totalA_nonhard_stage_correct (D : FieldData) (hq : 2 < D.q) :
    (totalA D).submatrix Subtype.val Subtype.val =
      nonHardFinish D * (nonHardLocal D * nonHardPrepare D) ∧
    (nonHardPrepare D).conjTranspose * nonHardPrepare D = 1 ∧
    (nonHardLocal D).conjTranspose * nonHardLocal D = 1 := by sorry
