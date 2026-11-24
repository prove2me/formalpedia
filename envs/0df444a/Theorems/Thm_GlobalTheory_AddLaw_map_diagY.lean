-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_map_diagY
-- name    : GlobalTheory.AddLaw.map_diagY
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:53:39.630533+00:00
-- url     : https://prove2.me/theorems/bb489850-3f86-4e89-adc5-a8d4b0103888
-- title:
--   Add Law: map diag Y
-- statement:
--   The Add Law construction uses the map diag Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L54-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {R S : Type*} [CommRing R] [CommRing S]
variable {W : Projective R}

theorem GlobalTheory.AddLaw.map_diagY (f : R →+* S) (P Q : Fin 3 → R) :
    diagY (W.map f) (f ∘ P) (f ∘ Q) = f (diagY W P Q) := by sorry
