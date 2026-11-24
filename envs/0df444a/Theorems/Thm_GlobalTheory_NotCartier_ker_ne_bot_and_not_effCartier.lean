-- Prove2me | Theorems.Thm_GlobalTheory_NotCartier_ker_ne_bot_and_not_effCartier
-- name    : GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:59:15.362943+00:00
-- url     : https://prove2.me/theorems/7eef2cfa-9b9e-47e4-8ebf-25f206890350
-- title:
--   Not Cartier: ker ne bot and not eff Cartier
-- statement:
--   The Not Cartier construction uses the ker ne bot and not eff Cartier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerNeBotAndNotEffCartier.lean#L41-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerNeBotAndNotEffCartier.lean#L41-L76

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

theorem GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y)
    [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) →
    i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by sorry
