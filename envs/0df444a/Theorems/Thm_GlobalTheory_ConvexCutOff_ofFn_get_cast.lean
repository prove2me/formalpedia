-- Prove2me | Theorems.Thm_GlobalTheory_ConvexCutOff_ofFn_get_cast
-- name    : GlobalTheory.ConvexCutOff.ofFn_get_cast
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:20.1728+00:00
-- url     : https://prove2.me/theorems/4ad280ba-47e4-4544-83da-923627b04f7b
-- title:
--   Convex Cut Off: of Fn get cast
-- statement:
--   The Convex Cut Off construction uses the of Fn get cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L151-L154

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory GlobalTheory.ConvexCutOff

theorem GlobalTheory.ConvexCutOff.ofFn_get_cast {α β : Type} (l : List α) {n : ℕ} (u : α → β) (h : n = l.length) :
    List.ofFn (fun k : Fin n => u (l.get (Fin.cast h k))) = l.map u := by sorry
