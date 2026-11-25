-- Prove2me | Theorems.Thm_GlobalTheory_ResidueCharacterDense_trace_base_change
-- name    : GlobalTheory.ResidueCharacterDense.trace_base_change
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:39.884383+00:00
-- url     : https://prove2.me/theorems/4a745977-7fe6-4d0f-8186-bad9fd79ed88
-- title:
--   Residue Character Dense: trace base change
-- statement:
--   The Residue Character Dense construction uses the trace base change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L72-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L72-L104

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense

theorem GlobalTheory.ResidueCharacterDense.trace_base_change {F E K L : Type} [Field F] [Field E] [Algebra F E] [Field K]
    [CommRing L] [Algebra K L] [Module.Free K L] (hE : Module.finrank F E = 2)
    (hL : Module.finrank K L = 2) (f : F →+* K) (g : E →+* L)
    (hc : ∀ a : F, g (algebraMap F E a) = algebraMap K L (f a))
    (hs : Submodule.span K (Set.range g) = ⊤) (x : E) :
    Algebra.trace K L (g x) = f (Algebra.trace F E x) := by sorry
