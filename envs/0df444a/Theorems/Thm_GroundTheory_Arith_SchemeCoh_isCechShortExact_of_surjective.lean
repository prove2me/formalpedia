-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isCechShortExact_of_surjective
-- name    : GroundTheory.Arith.SchemeCoh.isCechShortExact_of_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:58.1888+00:00
-- url     : https://prove2.me/theorems/37ac167a-61a8-4a74-b9db-9e66796f6bb0
-- title:
--   Scheme Coh: is Cech Short Exact of surjective
-- statement:
--   The Scheme Coh construction uses the is Cech Short Exact of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechLeray.lean#L320-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechLeray.lean#L320-L325

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
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
noncomputable section
open CategoryTheory Opposite TopologicalSpace Limits Abelian
universe w w' u
variable {X : TopCat.{u}}
variable {ι : Type w}

theorem GroundTheory.Arith.SchemeCoh.isCechShortExact_of_surjective {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : ι → Opens X)
    (hsurj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (S.g.hom.app (op (inter U i)))) :
    IsCechShortExact U S.f.hom S.g.hom := by sorry
