-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Fibre_hasProd_single
-- name    : GlobalTheory.CMVal.Fibre.hasProd_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:04:28.179434+00:00
-- url     : https://prove2.me/theorems/9e99046e-ce1c-446b-918d-2db5e93de6c4
-- title:
--   Fibre: has Prod single
-- statement:
--   The Fibre construction uses the has Prod single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L59-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L59-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Fibre
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Fibre.hasProd_single (y : (Af E)ˣ) : HasProd (fun P => single P (coord P y)) y := by sorry
