-- Prove2me | Theorems.Thm_GlobalTheory_T_ker_ne_bot_and_not_effCartier_of_two_le_dim
-- name    : GlobalTheory.T.ker_ne_bot_and_not_effCartier_of_two_le_dim
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:32.161529+00:00
-- url     : https://prove2.me/theorems/22df8924-2d1f-5fbf-942c-88cc08ede1fa
-- title:
--   T: ker ne bot and not eff Cartier of two le dim
-- statement:
--   The T construction uses the ker ne bot and not eff Cartier of two le dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerNeBotAndNotEffCartierStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerNeBotAndNotEffCartierStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerNeBotAndNotEffCartier
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerNeBotAndNotEffCartierStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ker_ne_bot_and_not_effCartier_of_two_le_dim : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y) [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) → i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by sorry
