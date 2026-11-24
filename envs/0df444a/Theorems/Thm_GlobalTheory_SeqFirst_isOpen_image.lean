-- Prove2me | Theorems.Thm_GlobalTheory_SeqFirst_isOpen_image
-- name    : GlobalTheory.SeqFirst.isOpen_image
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:09:55.930708+00:00
-- url     : https://prove2.me/theorems/d8ec95fa-cfb9-479b-b40a-3e685f61954a
-- title:
--   Seq First: is Open image
-- statement:
--   The Seq First construction uses the is Open image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoNearOrCentreMeets.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoNearOrCentreMeets.lean#L33-L45

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

theorem GlobalTheory.SeqFirst.isOpen_image {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {A : Set X}
    (hA : IsOpen A) : IsOpen (s '' (A ∩ s ⁻¹ᵁ U)) := by sorry
