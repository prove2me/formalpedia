-- Prove2me | Theorems.Thm_GlobalTheory_LevQuot_isOpenImmersion_graph
-- name    : GlobalTheory.LevQuot.isOpenImmersion_graph
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:11.474383+00:00
-- url     : https://prove2.me/theorems/ef23f6a5-4bbb-41f1-8f52-693520b9be21
-- title:
--   Lev Quot: is Open Immersion graph
-- statement:
--   The Lev Quot construction uses the is Open Immersion graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L10-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}

theorem GlobalTheory.LevQuot.isOpenImmersion_graph (r : X ⟶ Y) [Etale r] (f : X ⟶ X) (h : 𝟙 X ≫ r = f ≫ r) :
    IsOpenImmersion (pullback.lift (𝟙 X) f h) := by sorry
