-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_map_diagX
-- name    : GlobalTheory.AddLaw.map_diagX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:45:03.404941+00:00
-- url     : https://prove2.me/theorems/1f8ef540-f607-47e2-a696-999d9a89fd44
-- title:
--   Add Law: map diag X
-- statement:
--   The Add Law construction uses the map diag X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DiagZEqNegAddY.lean#L614-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DiagZEqNegAddY.lean#L614-L617

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

theorem GlobalTheory.AddLaw.map_diagX (f : R →+* S) (P Q : Fin 3 → R) :
    diagX (W.map f) (f ∘ P) (f ∘ Q) = f (diagX W P Q) := by sorry
