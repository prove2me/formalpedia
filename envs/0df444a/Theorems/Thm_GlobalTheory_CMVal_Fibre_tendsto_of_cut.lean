-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Fibre_tendsto_of_cut
-- name    : GlobalTheory.CMVal.Fibre.tendsto_of_cut
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:48.10971+00:00
-- url     : https://prove2.me/theorems/ac272f2c-984d-4129-886f-ba3474aed706
-- title:
--   Fibre: tendsto of cut
-- statement:
--   The Fibre construction uses the tendsto of cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L14-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L14-L40

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

theorem GlobalTheory.CMVal.Fibre.tendsto_of_cut (a : Af E) (g : Finset (HeightOneSpectrum (𝓞 E)) → Af E)
    (hg : ∀ T v, g T v = if v ∈ T then a v else 1) : Tendsto g atTop (𝓝 a) := by sorry
