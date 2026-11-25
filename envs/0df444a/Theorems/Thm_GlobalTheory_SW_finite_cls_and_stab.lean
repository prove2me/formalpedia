-- Prove2me | Theorems.Thm_GlobalTheory_SW_finite_cls_and_stab
-- name    : GlobalTheory.SW.finite_cls_and_stab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:00.239215+00:00
-- url     : https://prove2.me/theorems/3f124ae2-96d0-46ef-9c27-59e2b4d72a84
-- title:
--   SW: finite cls and stab
-- statement:
--   The SW construction uses the finite cls and stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClsAndStab.lean#L356-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClsAndStab.lean#L356-L380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real

theorem GlobalTheory.SW.finite_cls_and_stab : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (n M : ℕ), 0 < M → Finite (_root_.GlobalTheory.SW.Cls E n M) ∧
    _root_.GlobalTheory.SW.stdL E n ∈ _root_.GlobalTheory.SW.Vset E n M ∧
    (∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
      {h ∈ _root_.GlobalTheory.SW.DH E n M | _root_.GlobalTheory.SW.Moves h Λ Λ}.Finite ∧
        0 < _root_.GlobalTheory.SW.wt M Λ) ∧
    (1 ∈ _root_.GlobalTheory.SW.DH E n M ∧
      ∀ h ∈ _root_.GlobalTheory.SW.DH E n M,
        _root_.GlobalTheory.SW.ccT h ∈ _root_.GlobalTheory.SW.DH E n M ∧
          ∀ h' ∈ _root_.GlobalTheory.SW.DH E n M,
            h * h' ∈ _root_.GlobalTheory.SW.DH E n M) ∧
    ∀ h ∈ _root_.GlobalTheory.SW.DH E n M, ∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
      ∃ Λ' ∈ _root_.GlobalTheory.SW.Vset E n M, _root_.GlobalTheory.SW.Moves h Λ Λ' := by sorry
