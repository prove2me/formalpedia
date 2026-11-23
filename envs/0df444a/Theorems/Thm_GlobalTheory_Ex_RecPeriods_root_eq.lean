-- Prove2me | Theorems.Thm_GlobalTheory_Ex_RecPeriods_root_eq
-- name    : GlobalTheory.Ex.RecPeriods.root_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:23.248802+00:00
-- url     : https://prove2.me/theorems/167b414c-0024-4c49-a0f0-185e4094a632
-- title:
--   Rec Periods: root eq
-- statement:
--   The Rec Periods construction uses the root eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean#L216-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean#L216-L225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
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
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)

theorem GlobalTheory.Ex.RecPeriods.root_eq [IsAlgClosed C] (hn : Odd n) (hN : ∀ b : N.A, ∃ γ : N.Gt, γ.b = b) {g' : ℕ} (ht : N'.Tors n g')
    {e : N.X ≃+ N'.X} (hB : μ.B e) (hT : μ.Term e) {I : NumB.Iso N.toNumB N'.toNumB} (hI : μ.OnB I) (j : ℕ) (hj : 1 ≤ j)
    (p₁ : N.QT (n ^ j)) (p₁' : N'.QT (n ^ j)) (h₁ : μ.r _ p₁ p₁') (he : p₁'.1.1.toAdd = e p₁.1.1.toAdd) :
    p₁'.1.2.b = I.φ p₁.1.2.b := by sorry
