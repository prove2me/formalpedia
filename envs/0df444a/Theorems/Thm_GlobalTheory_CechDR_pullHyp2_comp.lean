-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_pullHyp2_comp
-- name    : GlobalTheory.CechDR.pullHyp2_comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:34:36.723569+00:00
-- url     : https://prove2.me/theorems/93362ad2-a3ed-4dd5-b62e-4935b03160f3
-- title:
--   Cech DR: pull Hyp2 comp
-- statement:
--   The Cech DR construction uses the pull Hyp2 comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamCoefMapOneFormsRestrictAlongFunctor.lean#L181-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamCoefMapOneFormsRestrictAlongFunctor.lean#L181-L186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

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

theorem GlobalTheory.CechDR.pullHyp2_comp (n : CoefMap τ F' F'') (c : Hyp2 F) :
    pullHyp2 (m.comp n) c = pullHyp2 n (pullHyp2 m c) := by sorry
