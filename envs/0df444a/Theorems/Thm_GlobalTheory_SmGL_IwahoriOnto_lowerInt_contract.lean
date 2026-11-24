-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_lowerInt_contract
-- name    : GlobalTheory.SmGL.IwahoriOnto.lowerInt_contract
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:56.722612+00:00
-- url     : https://prove2.me/theorems/db8079ed-d3e1-4507-97da-567ccd1baa02
-- title:
--   Iwahori Onto: lower Int contract
-- statement:
--   The Iwahori Onto construction uses the lower Int contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L196-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L196-L240

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

theorem GlobalTheory.SmGL.IwahoriOnto.lowerInt_contract : ∀ U ∈ 𝓝 (1 : GL n k), ∃ t : n → kˣ, ∀ c ∈ lowerInt k n,
    (diagT k n t)⁻¹ * c * diagT k n t ∈ U := by sorry
