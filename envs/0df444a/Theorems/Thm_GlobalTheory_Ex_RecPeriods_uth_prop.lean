-- Prove2me | Theorems.Thm_GlobalTheory_Ex_RecPeriods_uth_prop
-- name    : GlobalTheory.Ex.RecPeriods.uth_prop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:51.955964+00:00
-- url     : https://prove2.me/theorems/86e6e8cb-4c6b-4912-95d4-501a58719998
-- title:
--   Rec Periods: uth prop
-- statement:
--   The Rec Periods construction uses the uth prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean#L189-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean#L189-L214

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

theorem GlobalTheory.Ex.RecPeriods.uth_prop [IsAlgClosed C] (hn : Odd n) (hN : ∀ b : N.A, ∃ γ : N.Gt, γ.b = b) {e : N.X ≃+ N'.X} (hB : μ.B e)
    (hT : μ.Term e) {I : NumB.Iso N.toNumB N'.toNumB} (hI : μ.OnB I) (j : ℕ) (p₁ : N.QT (n ^ j)) (p₁' : N'.QT (n ^ j))
    (h₁ : μ.r _ p₁ p₁') (he : p₁'.1.1.toAdd = e p₁.1.1.toAdd) (b : N.A) (hb : b ^ (n ^ j) ^ 2 = 1) :
    (N'.ψ (e p₁.1.1.toAdd) * mulq N'.θ N'.σ (n ^ j) p₁'.1.2.b * (I.lam * I.h p₁.1.2.b ^ (n ^ j) ^ 2) : Cˣ) *
      N'.uth (n ^ j) (I.φ b) p₁'.1.2.b =
    μ.c₀ * (N.ψ p₁.1.1.toAdd * mulq N.θ N.σ (n ^ j) p₁.1.2.b : Cˣ) * N'.uth (n ^ j) (I.φ b) (I.φ p₁.1.2.b) := by sorry
