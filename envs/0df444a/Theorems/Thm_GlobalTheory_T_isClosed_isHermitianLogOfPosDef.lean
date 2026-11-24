-- Prove2me | Theorems.Thm_GlobalTheory_T_isClosed_isHermitianLogOfPosDef
-- name    : GlobalTheory.T.isClosed_isHermitianLogOfPosDef
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:48.237339+00:00
-- url     : https://prove2.me/theorems/770f163e-af38-449b-8b3c-81fb33015f9e
-- title:
--   T: is Closed is Hermitian Log Of Pos Def
-- statement:
--   The T construction uses the is Closed is Hermitian Log Of Pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsClosedIsHermitianLogOfPosDefStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsClosedIsHermitianLogOfPosDefStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsClosedIsHermitianLogOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsClosedIsHermitianLogOfPosDefStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isClosed_isHermitianLogOfPosDef : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], IsClosed {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} := by sorry
