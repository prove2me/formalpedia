-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_cechDeRhamCoefMapOneForms_eq_of_natTrans
-- name    : GlobalTheory.CechDR.cechDeRhamCoefMapOneForms_eq_of_natTrans
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:32:56.813629+00:00
-- url     : https://prove2.me/theorems/a0876a26-7496-4859-a831-7fe3234d84aa
-- title:
--   Cech DR: cech De Rham Coef Map One Forms eq of nat Trans
-- statement:
--   The Cech DR construction uses the cech De Rham Coef Map One Forms eq of nat Trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamCoefMapOneFormsRestrictAlongFunctor.lean#L194-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamCoefMapOneFormsRestrictAlongFunctor.lean#L194-L195

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
variable {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
  (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b)
include h

theorem GlobalTheory.CechDR.cechDeRhamCoefMapOneForms_eq_of_natTrans (T : C') (ω : Ω[F.obj (m.G.obj T)⁄R]) : q1 m' T (p1 F (θ.app T) ω) = q1 m T ω := by sorry
