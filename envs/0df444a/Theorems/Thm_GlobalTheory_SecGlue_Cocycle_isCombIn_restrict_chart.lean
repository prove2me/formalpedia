-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Cocycle_isCombIn_restrict_chart
-- name    : GlobalTheory.SecGlue.Cocycle.isCombIn_restrict_chart
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:50:39.485029+00:00
-- url     : https://prove2.me/theorems/9cb5e5b8-56e2-4ecc-8a6e-e77637788368
-- title:
--   Cocycle: is Comb In restrict chart
-- statement:
--   The Cocycle construction uses the is Comb In restrict chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftsAgreeOfCocycle.lean#L50-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftsAgreeOfCocycle.lean#L50-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsAgreeOfCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Cocycle

theorem GlobalTheory.SecGlue.Cocycle.isCombIn_restrict_chart {Y : Scheme.{0}} {V V' : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') {S T S' : Type} [CommRing S] [CommRing T] [CommRing S']
    (q : S →+* T) (hq : Function.Surjective q) (h2 : RingHom.ker q ^ 2 = ⊥) (g : S →+* S')
    {ι : Type} [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S)
    (hw : ∀ i, spMap q ≫ w i = spMap q ≫ u) (hC : IsCombIn V u c w a)
    (hu : (spMap g ≫ u) ⁻¹ᵁ V' = ⊤) :
    IsCombIn V' (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by sorry
