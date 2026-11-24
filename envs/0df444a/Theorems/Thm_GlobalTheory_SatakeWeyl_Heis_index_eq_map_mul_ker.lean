-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_index_eq_map_mul_ker
-- name    : GlobalTheory.SatakeWeyl.Heis.index_eq_map_mul_ker
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:47:50.568865+00:00
-- url     : https://prove2.me/theorems/e891e0c3-b818-4542-bec2-ec3658ec1e7b
-- title:
--   Heis: index eq map mul ker
-- statement:
--   The Heis construction uses the index eq map mul ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L11-L27

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis

theorem GlobalTheory.SatakeWeyl.Heis.index_eq_map_mul_ker {A B : Type} [Group A] [Group B] (φ : A →* B) (V : Subgroup A) :
    V.index = (V.map φ).relIndex φ.range * V.relIndex φ.ker := by sorry
