-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_lower
-- name    : GlobalTheory.SmGL.JacquetFiniteLength.lower
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:38.642603+00:00
-- url     : https://prove2.me/theorems/b31bbac5-ba26-483c-b195-59db378a1b01
-- title:
--   Jacquet Finite Length: lower
-- statement:
--   The Jacquet Finite Length construction uses the lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfIsIrreducible.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfIsIrreducible.lean#L119-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory
open GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.SmGL.JacquetFiniteLength.lower (h : JacquetFiniteLength k) (e : (Σ a, m a) ≃ n)
    {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) (hl : HasFiniteLength π) :
    HasFiniteLength (jacLower e π) := by sorry
