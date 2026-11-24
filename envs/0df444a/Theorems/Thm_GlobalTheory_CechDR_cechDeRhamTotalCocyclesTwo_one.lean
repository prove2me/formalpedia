-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_one
-- name    : GlobalTheory.CechDR.cechDeRhamTotalCocyclesTwo.one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:10.698279+00:00
-- url     : https://prove2.me/theorems/b8348e9e-a0db-4214-adec-f64ec1284141
-- title:
--   cech De Rham Total Cocycles Two: one
-- statement:
--   The cech De Rham Total Cocycles Two construction uses the one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L260-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L260-L261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
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
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable {T T' T'' T''' : C}

theorem GlobalTheory.CechDR.cechDeRhamTotalCocyclesTwo.one (c : cechDeRhamTotalCocyclesTwo F) (φ : T ⟶ T') (ψ : T' ⟶ T'') : c.1.2.1 T T'' (φ ≫ ψ) =
    p1 F ψ (c.1.2.1 T T' φ) + c.1.2.1 T' T'' ψ + D R _ (c.1.1 T T' T'' φ ψ) := by sorry
