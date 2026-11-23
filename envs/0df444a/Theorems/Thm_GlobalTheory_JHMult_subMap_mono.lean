-- Prove2me | Theorems.Thm_GlobalTheory_JHMult_subMap_mono
-- name    : GlobalTheory.JHMult.subMap_mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:36.981158+00:00
-- url     : https://prove2.me/theorems/a5d4f4f4-81b7-48ce-93f1-f36655764ae9
-- title:
--   JHMult: sub Map mono
-- statement:
--   The JHMult construction uses the sub Map mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L35-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.JHMult
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

theorem GlobalTheory.JHMult.subMap_mono {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    (p : ρ.IntertwiningMap ρ₁) {S T : Subrepresentation ρ} (h : S ≤ T) : subMap p S ≤ subMap p T := by sorry
