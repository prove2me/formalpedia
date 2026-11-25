-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_local_section_of_isIntegralElem_normal_scheme
-- name    : GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:13.369122+00:00
-- url     : https://prove2.me/theorems/ce136f34-aa15-572b-a5bd-9180ddcd2134
-- title:
--   T: exists local section of is Integral Elem normal scheme
-- statement:
--   The T construction uses the exists local section of is Integral Elem normal scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalSectionOfIsIntegralElemNormalSchemeStatement.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalSectionOfIsIntegralElemNormalSchemeStatement.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLocalSectionOfIsIntegralElemNormalScheme
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLocalSectionOfIsIntegralElemNormalSchemeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme : ∀ {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j],
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by sorry
