-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_goodAcyclic_modulesAb
-- name    : GroundTheory.Arith.SchemeCoh.goodAcyclic_modulesAb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:27.874042+00:00
-- url     : https://prove2.me/theorems/505c776e-4ea1-4eef-a039-f8f817a29fb1
-- title:
--   Scheme Coh: good Acyclic modules Ab
-- statement:
--   The Scheme Coh construction uses the good Acyclic modules Ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechSeparated.lean#L141-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechSeparated.lean#L141-L144

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

theorem GroundTheory.Arith.SchemeCoh.goodAcyclic_modulesAb (F : X.Modules) [F.IsQuasicoherent] :
    GoodAcyclic (X := X.toTopCat) IsAffineOpen (fun {κ} V U => IsBasicCover (κ := κ) V U)
      (modulesAb F) := by sorry
