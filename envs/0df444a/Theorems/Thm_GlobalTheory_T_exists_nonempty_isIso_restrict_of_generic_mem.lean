-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_nonempty_isIso_restrict_of_generic_mem
-- name    : GlobalTheory.T.exists_nonempty_isIso_restrict_of_generic_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:37.621482+00:00
-- url     : https://prove2.me/theorems/76403a5d-208e-5caf-b7f6-0f8d8ff3714e
-- title:
--   T: exists nonempty is Iso restrict of generic mem
-- statement:
--   The T construction uses the exists nonempty is Iso restrict of generic mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoRestrictOfClosedImmersionNearGenericStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoRestrictOfClosedImmersionNearGenericStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoRestrictOfClosedImmersionNearGeneric
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoRestrictOfClosedImmersionNearGenericStatement
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

theorem GlobalTheory.T.exists_nonempty_isIso_restrict_of_generic_mem : ∀ {W W' Y Y₁ : Scheme.{0}} [IsIntegral W] [IsIntegral W'] (i : W ⟶ Y) [IsClosedImmersion i] (h : W' ⟶ W) (c : W' ⟶ Y₁) [IsClosedImmersion c] (s₁ : Y₁ ⟶ Y) (U : Y.Opens), IsIso (s₁ ∣_ U) → h ≫ i = c ≫ s₁ → i (genericPoint W) ∈ U → (∃ w', h w' = genericPoint W) → ∃ U' : W.Opens, (U' : Set W).Nonempty ∧ IsIso (h ∣_ U') := by sorry
