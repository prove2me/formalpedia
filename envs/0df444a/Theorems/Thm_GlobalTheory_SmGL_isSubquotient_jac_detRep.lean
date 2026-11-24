-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_isSubquotient_jac_detRep
-- name    : GlobalTheory.SmGL.isSubquotient_jac_detRep
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:13:50.944687+00:00
-- url     : https://prove2.me/theorems/e653ff59-9b9e-46a3-becc-73010cd555d3
-- title:
--   Sm GL: is Subquotient jac det Rep
-- statement:
--   The Sm GL construction uses the is Subquotient jac det Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L551-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L551-L557

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem GlobalTheory.SmGL.isSubquotient_jac_detRep (e : (Σ a, m a) ≃ n) (χ : kˣ →* ℂˣ) :
    IsSubquotient (ofChar (detLevi e χ)) (jac e (detRep n χ)) := by sorry
