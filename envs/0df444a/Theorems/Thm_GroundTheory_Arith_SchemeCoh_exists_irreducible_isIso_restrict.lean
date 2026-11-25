-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_exists_irreducible_isIso_restrict
-- name    : GroundTheory.Arith.SchemeCoh.exists_irreducible_isIso_restrict
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:37.257788+00:00
-- url     : https://prove2.me/theorems/d24ce0d7-1c34-45c4-a8fe-c1abf3d5a99a
-- title:
--   Scheme Coh: exists irreducible is Iso restrict
-- statement:
--   The Scheme Coh construction uses the exists irreducible is Iso restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/IrreducibleImage.lean#L23-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/IrreducibleImage.lean#L23-L50

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SchemeImage
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_IrreducibleImage
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
universe u
noncomputable section

theorem GroundTheory.Arith.SchemeCoh.exists_irreducible_isIso_restrict (Z : Scheme.{u}) [IsNoetherian Z] [Nonempty Z] :
    ∃ (Z₁ : Scheme.{u}) (c : Z₁ ⟶ Z) (O : Z.Opens), IsClosedImmersion c ∧ IrreducibleSpace Z₁ ∧
      (O : Set Z).Nonempty ∧ IsIso (c ∣_ O) := by sorry
