-- Prove2me | Theorems.Thm_GlobalTheory_exists_section_of_isIntegralElem_of_isOpenImmersion
-- name    : GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:12.315051+00:00
-- url     : https://prove2.me/theorems/221e038c-b6f4-4467-89f3-c1a29f27793e
-- title:
--   Global Theory: exists section of is Integral Elem of is Open Immersion
-- statement:
--   The Global Theory construction uses the exists section of is Integral Elem of is Open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalSectionOfIsIntegralElemNormalScheme.lean#L7-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalSectionOfIsIntegralElemNormalScheme.lean#L7-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLocalSectionOfIsIntegralElemNormalScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory

theorem GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion {T Z : Scheme.{0}}
    [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j] :
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by sorry
