-- Prove2me | Theorems.Thm_GlobalTheory_app_injective_of_dense_range
-- name    : GlobalTheory.app_injective_of_dense_range
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:36.100814+00:00
-- url     : https://prove2.me/theorems/eae519df-721e-4d5b-b676-88c10882ddea
-- title:
--   Global Theory: app injective of dense range
-- statement:
--   The Global Theory construction uses the app injective of dense range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueOfDenseOpenImmersion.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueOfDenseOpenImmersion.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueOfDenseOpenImmersion
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

theorem GlobalTheory.app_injective_of_dense_range {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (W : Z.Opens) : Function.Injective (j.app W).hom := by sorry
