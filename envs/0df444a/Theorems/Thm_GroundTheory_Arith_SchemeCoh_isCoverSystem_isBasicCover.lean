-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isCoverSystem_isBasicCover
-- name    : GroundTheory.Arith.SchemeCoh.isCoverSystem_isBasicCover
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:48.029301+00:00
-- url     : https://prove2.me/theorems/115d9eb9-9003-4668-a49b-83981a243107
-- title:
--   Scheme Coh: is Cover System is Basic Cover
-- statement:
--   The Scheme Coh construction uses the is Cover System is Basic Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechSeparated.lean#L69-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechSeparated.lean#L69-L90

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe w w' u
variable {X : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.isCoverSystem_isBasicCover :
    IsCoverSystem (X := X.toTopCat) IsAffineOpen (fun {κ} V U => IsBasicCover (κ := κ) V U) := by sorry
