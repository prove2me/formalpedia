-- Prove2me | Theorems.Thm_GlobalTheory_NotCartier_ringKrullDim_stalk_le_one
-- name    : GlobalTheory.NotCartier.ringKrullDim_stalk_le_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:59:41.07317+00:00
-- url     : https://prove2.me/theorems/a10969c6-0f45-4456-ba46-61b222544084
-- title:
--   Not Cartier: ring Krull Dim stalk le one
-- statement:
--   The Not Cartier construction uses the ring Krull Dim stalk le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerNeBotAndNotEffCartier.lean#L9-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerNeBotAndNotEffCartier.lean#L9-L35

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerNeBotAndNotEffCartier
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
noncomputable section
open GlobalTheory GlobalTheory.NotCartier

theorem GlobalTheory.NotCartier.ringKrullDim_stalk_le_one {X : Scheme.{0}} [IsLocallyNoetherian X] (J : X.IdealSheafData) (x : X)
    (hx : x ∈ J.support) (hmin : ∀ z ∈ J.support, z ⤳ x → z = x) (V : X.affineOpens) (hxV : x ∈ V.1)
    (hP : (J.ideal V).IsPrincipal) : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by sorry
