-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_coneMap_mk
-- name    : GlobalTheory.CechDR.coneMap_mk
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:45.810107+00:00
-- url     : https://prove2.me/theorems/eb403b2d-a6d1-4e4a-b5a4-d25357a9f972
-- title:
--   Cech DR: cone Map mk
-- statement:
--   The Cech DR construction uses the cone Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamCoefMapOneFormsRestrictAlongFunctor.lean#L266-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamCoefMapOneFormsRestrictAlongFunctor.lean#L266-L267

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
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B} {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)

theorem GlobalTheory.CechDR.coneMap_mk (ω : LinearMap.ker (dOne R B)) :
    coneMap e he (Submodule.Quotient.mk ω) = ofForm F (coneForm e he ω) := by sorry
