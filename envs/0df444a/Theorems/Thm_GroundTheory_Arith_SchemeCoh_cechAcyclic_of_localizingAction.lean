-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_cechAcyclic_of_localizingAction
-- name    : GroundTheory.Arith.SchemeCoh.cechAcyclic_of_localizingAction
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:19.519512+00:00
-- url     : https://prove2.me/theorems/63ce01aa-5d37-45c2-adeb-141084690aef
-- title:
--   Scheme Coh: cech Acyclic of localizing Action
-- statement:
--   The Scheme Coh construction uses the cech Acyclic of localizing Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L168-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L168-L193

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
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
open CategoryTheory Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable {D : R → Opens X} (A : LocalizingAction P D)
variable {ι : Type u} (U : ι → Opens X)
variable (h : ι → R)
include A

theorem GroundTheory.Arith.SchemeCoh.cechAcyclic_of_localizingAction [Finite ι] (g : R) (hcov : ⨆ i, D (h i) = D g) :
    CechAcyclic P (D ∘ h) := by sorry
