-- Prove2me | Theorems.Thm_GlobalTheory_LevQuot_appLE_congr_hom
-- name    : GlobalTheory.LevQuot.appLE_congr_hom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:07.988588+00:00
-- url     : https://prove2.me/theorems/592957f4-dee4-4c3a-9688-60fa48e351f8
-- title:
--   Lev Quot: app LE congr hom
-- statement:
--   The Lev Quot construction uses the app LE congr hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L24-L26

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

theorem GlobalTheory.LevQuot.appLE_congr_hom {Z : Scheme.{0}} {f g : Z ⟶ X} (e : f = g) (U : X.Opens) (V : Z.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by sorry
