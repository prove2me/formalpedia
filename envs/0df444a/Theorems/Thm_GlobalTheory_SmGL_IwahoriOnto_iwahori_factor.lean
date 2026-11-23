-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_iwahori_factor
-- name    : GlobalTheory.SmGL.IwahoriOnto.iwahori_factor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:15.190428+00:00
-- url     : https://prove2.me/theorems/adcee6fe-3765-4142-81e5-a2926280f694
-- title:
--   Iwahori Onto: iwahori factor
-- statement:
--   The Iwahori Onto construction uses the iwahori factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L167-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L167-L194

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

theorem GlobalTheory.SmGL.IwahoriOnto.iwahori_factor : ∀ g ∈ iwahori k n, ∃ d ∈ torusO k n, ∃ x ∈ unipB k n, ∃ c ∈ lowerInt k n,
    g = diagT k n d * x * c := by sorry
