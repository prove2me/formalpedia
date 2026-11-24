-- Prove2me | Theorems.Thm_GlobalTheory_ThetaOnto_mem_span_of_card_le
-- name    : GlobalTheory.ThetaOnto.mem_span_of_card_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:16.645665+00:00
-- url     : https://prove2.me/theorems/38ca725d-76ff-45fe-8e2b-366f73b8386f
-- title:
--   Theta Onto: mem span of card le
-- statement:
--   The Theta Onto construction uses the mem span of card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemSpanOfCardLe.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemSpanOfCardLe.lean#L45-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanOfCardLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaOnto

theorem GlobalTheory.ThetaOnto.mem_span_of_card_le {V : Type} [AddCommGroup V] [Module ℂ V] (Q : V → Prop) {N : ℕ}
    (hN : ∀ (M : ℕ) (f : Fin M → V), (∀ k, Q (f k)) → LinearIndependent ℂ f → M ≤ N)
    (f : Fin N → V) (hf : ∀ k, Q (f k)) (hli : LinearIndependent ℂ f) {v : V} (hv : Q v) :
    ∃ a : Fin N → ℂ, ∑ i, a i • f i = v := by sorry
