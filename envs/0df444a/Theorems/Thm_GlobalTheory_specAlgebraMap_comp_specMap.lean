-- Prove2me | Theorems.Thm_GlobalTheory_specAlgebraMap_comp_specMap
-- name    : GlobalTheory.specAlgebraMap_comp_specMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:51:35.316796+00:00
-- url     : https://prove2.me/theorems/51fe100f-82ff-4e42-95c8-f8c5762ae2fe
-- title:
--   Global Theory: spec Algebra Map comp spec Map
-- statement:
--   The Global Theory construction uses the spec Algebra Map comp spec Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L102-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {V K : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {X X' S S' : Scheme.{u}}
variable (p : X ⟶ S) [UniversallyClosed p] [IsSeparated p] (r : Spec (.of V) ⟶ S)
  (y : Spec (.of K) ⟶ X) (h : y ≫ p = specAlgebraMap V K ≫ r)
variable {V' K' : Type u} [CommRing V'] [IsDomain V'] [ValuationRing V'] [Field K']
  [Algebra V' K'] [IsFractionRing V' K']
omit [IsDomain V] [ValuationRing V] [IsFractionRing V K] [IsDomain V'] [ValuationRing V']
  [IsFractionRing V' K']

theorem GlobalTheory.specAlgebraMap_comp_specMap (ψ : V →+* V') (χ : K →+* K')
    (w : χ.comp (algebraMap V K) = (algebraMap V' K').comp ψ) :
    specAlgebraMap V' K' ≫ Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom χ) ≫ specAlgebraMap V K := by sorry
