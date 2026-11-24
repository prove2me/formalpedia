-- Prove2me | Theorems.Thm_GlobalTheory_SeqFirst_isIso_restrict_of_le
-- name    : GlobalTheory.SeqFirst.isIso_restrict_of_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:10:03.757843+00:00
-- url     : https://prove2.me/theorems/87920fa9-b525-4557-913e-8f3a8926fc95
-- title:
--   Seq First: is Iso restrict of le
-- statement:
--   The Seq First construction uses the is Iso restrict of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoNearOrCentreMeets.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoNearOrCentreMeets.lean#L8-L15

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoNearOrCentreMeets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.SeqFirst

theorem GlobalTheory.SeqFirst.isIso_restrict_of_le {X Y : Scheme.{0}} (s : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U)
    [IsIso (s ∣_ U)] : IsIso (s ∣_ V) := by sorry
