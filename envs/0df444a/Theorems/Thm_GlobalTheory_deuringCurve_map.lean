-- Prove2me | Theorems.Thm_GlobalTheory_deuringCurve_map
-- name    : GlobalTheory.deuringCurve_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:15:58.579587+00:00
-- url     : https://prove2.me/theorems/d3f99c95-b9b5-4d73-a7ab-7fb85a21c098
-- title:
--   Global Theory: deuring Curve map
-- statement:
--   The Global Theory construction uses the deuring Curve map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L88-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {R : Type*} [CommRing R]

theorem GlobalTheory.deuringCurve_map {S : Type*} [CommRing S] (f : R →+* S) (a b : R) :
    (deuringCurve a b).map f = deuringCurve (f a) (f b) := by sorry
