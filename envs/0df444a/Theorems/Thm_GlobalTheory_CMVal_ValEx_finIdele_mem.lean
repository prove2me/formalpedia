-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_finIdele_mem
-- name    : GlobalTheory.CMVal.ValEx.finIdele_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:42.182156+00:00
-- url     : https://prove2.me/theorems/d301a4db-7828-4aab-a8ff-d26594a519d7
-- title:
--   Val Ex: fin Idele mem
-- statement:
--   The Val Ex construction uses the fin Idele mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L406-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L406-L411

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.ValEx.finIdele_mem {P : HeightOneSpectrum (𝓞 E)} {y : (Af E)ˣ} (h : SuppAt P y) (h1 : Valued.v ((y : Af E) P) = 1) :
    finIdele E y ∈ unitI := by sorry
