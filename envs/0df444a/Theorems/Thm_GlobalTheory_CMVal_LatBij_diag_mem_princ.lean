-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_LatBij_diag_mem_princ
-- name    : GlobalTheory.CMVal.LatBij.diag_mem_princ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:02.554414+00:00
-- url     : https://prove2.me/theorems/fdf4ee82-f33d-4293-8bfc-eb53f4da5c1d
-- title:
--   Lat Bij: diag mem princ
-- statement:
--   The Lat Bij construction uses the diag mem princ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticePointsIntegralIdelesEquiv.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticePointsIntegralIdelesEquiv.lean#L19-L19

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticePointsIntegralIdelesEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.LatBij
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.LatBij.diag_mem_princ (a : Eˣ) : diag a ∈ (princ : Subgroup (Af E)ˣ) := by sorry
