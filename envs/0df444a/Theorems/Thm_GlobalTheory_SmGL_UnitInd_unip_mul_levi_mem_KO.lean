-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnitInd_unip_mul_levi_mem_KO
-- name    : GlobalTheory.SmGL.UnitInd.unip_mul_levi_mem_KO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:35.286088+00:00
-- url     : https://prove2.me/theorems/982cb6b4-00bf-43fc-b66b-df31e638debf
-- title:
--   Unit Ind: unip mul levi mem KO
-- statement:
--   The Unit Ind construction uses the unip mul levi mem KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L220-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L220-L243

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)

theorem GlobalTheory.SmGL.UnitInd.unip_mul_levi_mem_KO (u : unipRad k e) (g : Levi k m) :
    (u : GL n k) * leviEmb k e g ∈ KO k n ↔ (u : GL n k) ∈ KO k n ∧ ∀ a, g a ∈ KO k (m a) := by sorry
