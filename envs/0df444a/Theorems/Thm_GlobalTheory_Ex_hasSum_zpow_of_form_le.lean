-- Prove2me | Theorems.Thm_GlobalTheory_Ex_hasSum_zpow_of_form_le
-- name    : GlobalTheory.Ex.hasSum_zpow_of_form_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:06:39.525529+00:00
-- url     : https://prove2.me/theorems/ff3d3f17-90b8-43ea-b7f0-41cbf15297b2
-- title:
--   Ex: has Sum zpow of form le
-- statement:
--   The Ex construction uses the has Sum zpow of form le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTxEvEqMapArc.lean#L13-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTxEvEqMapArc.lean#L13-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumMapPowerSeriesMkFinsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTxEvEqMapArc
import Theorems.Thm_GlobalTheory_IsSiegel_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex

theorem GlobalTheory.Ex.hasSum_zpow_of_form_le {O C X : Type} [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (φ : PowerSeries O →+* C) (h1 : ∀ f, ‖φ f‖ ≤ 1) (hX : ‖φ PowerSeries.X‖ < 1) (u : Cˣ)
    (hu : (u : C) = φ PowerSeries.X) (B : LinearMap.BilinForm ℤ X) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (y : X) {m : ℕ} (hm : m ≠ 0) {D : ℤ} (hD : 0 < D) (E : X → ℤ)
    (hE : ∀ χ, B (y + m • χ) (y + m • χ) ≤ D * E χ) (a : X → O) :
    HasSum (fun χ => ((u ^ E χ : Cˣ) : C) * φ (PowerSeries.C (a χ)))
      (φ (PowerSeries.mk fun n => ∑ᶠ (χ : X) (_ : E χ = n), a χ)) := by sorry
