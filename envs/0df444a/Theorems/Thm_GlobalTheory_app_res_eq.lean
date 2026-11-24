-- Prove2me | Theorems.Thm_GlobalTheory_app_res_eq
-- name    : GlobalTheory.app_res_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:51.196162+00:00
-- url     : https://prove2.me/theorems/1de23401-e4e9-4a7e-8743-9e5047ee3d55
-- title:
--   Global Theory: app res eq
-- statement:
--   The Global Theory construction uses the app res eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueOfDenseOpenImmersion.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueOfDenseOpenImmersion.lean#L20-L25

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

theorem GlobalTheory.app_res_eq {T Z : Scheme.{0}} (j : T ⟶ Z) {V W : Z.Opens} (i : V ⟶ W)
    (i' : j ⁻¹ᵁ V ⟶ j ⁻¹ᵁ W) (a : Γ(Z, W)) :
    j.app V (Z.presheaf.map i.op a) = T.presheaf.map i'.op (j.app W a) := by sorry
