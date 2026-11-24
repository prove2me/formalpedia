-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Fibre_hasProd_loc
-- name    : GlobalTheory.CMVal.Fibre.hasProd_loc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:04:41.797592+00:00
-- url     : https://prove2.me/theorems/337ddda0-a6d1-4072-bb9a-abe1205155b8
-- title:
--   Fibre: has Prod loc
-- statement:
--   The Fibre construction uses the has Prod loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L74-L75

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

theorem GlobalTheory.CMVal.Fibre.hasProd_loc (χ : HChar E) (y : (Af E)ˣ) : HasProd (fun P => χ.loc P (coord P y)) (finPart χ y) := by sorry
