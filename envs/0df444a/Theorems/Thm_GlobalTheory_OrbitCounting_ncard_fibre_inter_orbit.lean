-- Prove2me | Theorems.Thm_GlobalTheory_OrbitCounting_ncard_fibre_inter_orbit
-- name    : GlobalTheory.OrbitCounting.ncard_fibre_inter_orbit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:37:24.600894+00:00
-- url     : https://prove2.me/theorems/bdc0f1c7-b543-4f6e-992a-ef5b647cc767
-- title:
--   Orbit Counting: ncard fibre inter orbit
-- statement:
--   The Orbit Counting construction uses the ncard fibre inter orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinsumOrbitsCountingPrincipleFiniteFibres.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinsumOrbitsCountingPrincipleFiniteFibres.lean#L13-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinsumOrbitsCountingPrincipleFiniteFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.OrbitCounting

theorem GlobalTheory.OrbitCounting.ncard_fibre_inter_orbit {G X Y : Type} [CommGroup G] [MulAction G X] [MulAction G Y]
    (π : X → Y) (hπ : ∀ (g : G) (x : X), π (g • x) = g • π x) (x0 : X) :
    {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0}.ncard =
      (MulAction.stabilizer G x0).relIndex (MulAction.stabilizer G (π x0)) := by sorry
