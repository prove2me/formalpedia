-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_goodAcyclic_of_shortExact
-- name    : GroundTheory.Arith.SchemeCoh.goodAcyclic_of_shortExact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:32.843091+00:00
-- url     : https://prove2.me/theorems/bdf542b6-29e9-48d3-bc02-f458b9439f3f
-- title:
--   Scheme Coh: good Acyclic of short Exact
-- statement:
--   The Scheme Coh construction uses the good Acyclic of short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechLeray.lean#L304-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechLeray.lean#L304-L312

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
variable (B : Opens X → Prop) (Good : ∀ {κ : Type u}, Opens X → (κ → Opens X) → Prop)
variable {B Good} (hC : IsCoverSystem B Good)
  {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
include hC hS

theorem GroundTheory.Arith.SchemeCoh.goodAcyclic_of_shortExact (hF : GoodAcyclic B Good S.X₁)
    (hI : ∀ (κ : Type u) (U : κ → Opens X), CechAcyclic S.X₂.obj U) :
    GoodAcyclic B Good S.X₃ := by sorry
