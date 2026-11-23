-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Fibre_prod_single_apply
-- name    : GlobalTheory.CMVal.Fibre.prod_single_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:18.611424+00:00
-- url     : https://prove2.me/theorems/c1c4084c-6aec-45b3-b9c5-d7a437033fa0
-- title:
--   Fibre: prod single apply
-- statement:
--   The Fibre construction uses the prod single apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L44-L55

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
open Classical

theorem GlobalTheory.CMVal.Fibre.prod_single_apply (y : (Af E)ˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) :
    ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E) v = if v ∈ T then (y : Af E) v else 1 := by sorry
