-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_isOpen_iwahori
-- name    : GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:29.690961+00:00
-- url     : https://prove2.me/theorems/8a0924f0-6814-4fd4-a650-74cdb06ca6d6
-- title:
--   Iwahori Onto: is Open iwahori
-- statement:
--   The Iwahori Onto construction uses the is Open iwahori property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L153-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L153-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IwahoriOnto
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]

theorem GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori : IsOpen (iwahori k n : Set (GL n k)) := by sorry
