-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_exists_affineCover_basis
-- name    : GroundTheory.Arith.SchemeCoh.exists_affineCover_basis
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:51:53.99783+00:00
-- url     : https://prove2.me/theorems/477977b7-6603-5ce0-9f3d-95ff1037a26a
-- title:
--   Scheme Coh: exists affine Cover basis
-- statement:
--   The Scheme Coh construction uses the exists affine Cover basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean#L196-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean#L196-L208

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_IsQuasicoherentTensorOfInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
universe u
noncomputable section
variable {X : Scheme.{u}}
variable {M M' L : X.Modules} {U V : X.Opens} {s : ((preMod X).obj L).obj (op U)}

theorem GroundTheory.Arith.SchemeCoh.exists_affineCover_basis (hL : IsInvertibleSheaf L) :
    ∃ (V : X → X.Opens) (s : ∀ x, ((preMod X).obj L).obj (op (V x))),
      (∀ x, IsAffineOpen (V x)) ∧ (∀ x, x ∈ V x) ∧
        ∀ x, IsBasisOn ((preMod X).obj L) (V x) (s x) := by sorry
