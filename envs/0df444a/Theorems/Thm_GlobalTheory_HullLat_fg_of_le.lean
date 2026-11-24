-- Prove2me | Theorems.Thm_GlobalTheory_HullLat_fg_of_le
-- name    : GlobalTheory.HullLat.fg_of_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:37.433234+00:00
-- url     : https://prove2.me/theorems/5765651e-d9fc-4510-a515-7d0e9a40d561
-- title:
--   Hull Lat: fg of le
-- statement:
--   The Hull Lat construction uses the fg of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMaximalOrderHullSelfDualStableLattice.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMaximalOrderHullSelfDualStableLattice.lean#L7-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMaximalOrderHullSelfDualStableLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.HullLat

theorem GlobalTheory.HullLat.fg_of_le {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {L X : Submodule R M} (hL : L.FG) (hX : X ≤ L) : X.FG := by sorry
