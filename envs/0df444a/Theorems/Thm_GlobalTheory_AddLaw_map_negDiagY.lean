-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_map_negDiagY
-- name    : GlobalTheory.AddLaw.map_negDiagY
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:53:48.910797+00:00
-- url     : https://prove2.me/theorems/95b9b48f-0528-400b-a7df-0693ebdbbb1d
-- title:
--   Add Law: map neg Diag Y
-- statement:
--   The Add Law construction uses the map neg Diag Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DiagZEqNegAddY.lean#L619-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DiagZEqNegAddY.lean#L619-L622

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
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

theorem GlobalTheory.AddLaw.map_negDiagY (f : R →+* S) (P Q : Fin 3 → R) :
    negDiagY (W.map f) (f ∘ P) (f ∘ Q) = f (negDiagY W P Q) := by sorry
