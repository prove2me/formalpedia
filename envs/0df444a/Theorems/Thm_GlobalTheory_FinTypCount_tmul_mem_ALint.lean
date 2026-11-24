-- Prove2me | Theorems.Thm_GlobalTheory_FinTypCount_tmul_mem_ALint
-- name    : GlobalTheory.FinTypCount.tmul_mem_ALint
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:36.690141+00:00
-- url     : https://prove2.me/theorems/68293567-9163-4bd4-ad10-11d126c7ec14
-- title:
--   Fin Typ Count: tmul mem ALint
-- statement:
--   The Fin Typ Count construction uses the tmul mem ALint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L19-L26

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem GlobalTheory.FinTypCount.tmul_mem_ALint (o : 𝓞 L) {a : AFplus L} (ha : ∀ v, a v ∈ v.adicCompletionIntegers L⁺) :
    ((o : L) ⊗ₜ[L⁺] a : AL L) ∈ ALint L := by sorry
