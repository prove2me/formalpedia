-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarLevel_perSub_eq_range
-- name    : GlobalTheory.SW.HaarLevel.perSub_eq_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:14.688649+00:00
-- url     : https://prove2.me/theorems/42d2a530-42af-4dfe-bdd3-1bf2f69a626b
-- title:
--   Haar Level: per Sub eq range
-- statement:
--   The Haar Level construction uses the per Sub eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L58-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
omit [NumberField K] [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.HaarLevel.perSub_eq_range (R : ℕ) :
    perSub K κ ι R = ((incl K κ ι).comp (nsmulAddMonoidHom R)).range := by sorry
