-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_pullHyp2_mk
-- name    : GlobalTheory.CechDR.pullHyp2_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:34:34.478824+00:00
-- url     : https://prove2.me/theorems/8a53f118-e809-4e23-b18e-60cc75714f9e
-- title:
--   Cech DR: pull Hyp2 mk
-- statement:
--   The Cech DR construction uses the pull Hyp2 mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamCoefMapOneFormsRestrictAlongFunctor.lean#L133-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamCoefMapOneFormsRestrictAlongFunctor.lean#L133-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')

theorem GlobalTheory.CechDR.pullHyp2_mk (c : cechDeRhamTotalCocyclesTwo F) : pullHyp2 m (Hyp2.mk F c) = Hyp2.mk F' (pullZZ2 m c) := by sorry
