-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_section_extending_of_dense_openImmersion
-- name    : GlobalTheory.T.exists_section_extending_of_dense_openImmersion
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:14.686193+00:00
-- url     : https://prove2.me/theorems/4e7a51ed-8984-4afb-acc9-165823272db3
-- title:
--   T: exists section extending of dense open Immersion
-- statement:
--   The T construction uses the exists section extending of dense open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueOfDenseOpenImmersionStatement.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueOfDenseOpenImmersionStatement.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueOfDenseOpenImmersion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueOfDenseOpenImmersionStatement
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

theorem GlobalTheory.T.exists_section_extending_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by sorry
