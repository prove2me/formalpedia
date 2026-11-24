-- Prove2me | Theorems.Thm_GlobalTheory_ConvexCutOff_exists_perm_of_ofFn_perm
-- name    : GlobalTheory.ConvexCutOff.exists_perm_of_ofFn_perm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:02:41.025827+00:00
-- url     : https://prove2.me/theorems/fb4bbbbe-8eea-4ca4-9eae-f3814fd58564
-- title:
--   Convex Cut Off: exists perm of of Fn perm
-- statement:
--   The Convex Cut Off construction uses the exists perm of of Fn perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L131-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L131-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
import Theorems.Thm_GlobalTheory_FiberCardPermutation_exists_perm_of_ofFn_perm

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

theorem GlobalTheory.ConvexCutOff.exists_perm_of_ofFn_perm {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : (List.ofFn v).Perm (List.ofFn w)) : ∃ σ : Equiv.Perm (Fin n), v = w ∘ σ := by sorry
