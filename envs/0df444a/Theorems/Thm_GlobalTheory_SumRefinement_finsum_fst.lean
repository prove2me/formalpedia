-- Prove2me | Theorems.Thm_GlobalTheory_SumRefinement_finsum_fst
-- name    : GlobalTheory.SumRefinement.finsum_fst
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:45:04.328978+00:00
-- url     : https://prove2.me/theorems/31271ced-038c-4ff1-9cbf-1c9bcf85e523
-- title:
--   Sum Refinement: finsum fst
-- statement:
--   The Sum Refinement construction uses the finsum fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumRefine.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumRefine.lean#L5-L16

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SumRefinement

theorem GlobalTheory.SumRefinement.finsum_fst {X F : Type} [Finite F] (g : X → ℂ) (hg : (Function.support g).Finite) :
    ∑ᶠ p : X × F, g p.1 = (Nat.card F : ℂ) * ∑ᶠ x, g x := by sorry
