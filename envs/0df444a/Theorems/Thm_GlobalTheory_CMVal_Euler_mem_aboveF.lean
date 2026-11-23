-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_mem_aboveF
-- name    : GlobalTheory.CMVal.Euler.mem_aboveF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:23.148451+00:00
-- url     : https://prove2.me/theorems/fc05a395-330a-47fb-b255-7f2aa1b4cf79
-- title:
--   Euler: mem above F
-- statement:
--   The Euler construction uses the mem above F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L68-L72

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Euler.mem_aboveF (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) :
    P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v ↔ Over P v := by sorry
