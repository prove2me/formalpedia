-- Prove2me | Theorems.Thm_GlobalTheory_apply_valCentre_base
-- name    : GlobalTheory.apply_valCentre_base
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:46.298721+00:00
-- url     : https://prove2.me/theorems/4c9a7f48-533b-5b5c-953c-c031a9fbc7ff
-- title:
--   Global Theory: apply val Centre base
-- statement:
--   The Global Theory construction uses the apply val Centre base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L110-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L110-L111

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

theorem GlobalTheory.apply_valCentre_base : p (valCentre p r y h) = r (closedPoint V) := by sorry
