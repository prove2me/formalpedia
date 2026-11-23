-- Prove2me | Theorems.Thm_GlobalTheory_specMap_apply_eq_bot
-- name    : GlobalTheory.specMap_apply_eq_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:33.774332+00:00
-- url     : https://prove2.me/theorems/98323994-16bd-46e8-bbe9-f37c02a04a0c
-- title:
--   Global Theory: spec Map apply eq bot
-- statement:
--   The Global Theory construction uses the spec Map apply eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L283-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L283-L288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

theorem GlobalTheory.specMap_apply_eq_bot {R F : Type u} [CommRing R] [IsDomain R] [Field F] (g : R →+* F)
    (hg : Function.Injective g) (t : Spec (.of F)) :
    Spec.map (CommRingCat.ofHom g) t = (⊥ : PrimeSpectrum R) := by sorry
