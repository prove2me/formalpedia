-- Prove2me | Theorems.Thm_GlobalTheory_Ex_RecPeriods_c_psi
-- name    : GlobalTheory.Ex.RecPeriods.c_psi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:07:01.636181+00:00
-- url     : https://prove2.me/theorems/91e645ba-abfe-435a-bcb8-cb588e7ab32e
-- title:
--   Rec Periods: c psi
-- statement:
--   The Rec Periods construction uses the c psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean#L227-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean#L227-L254

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

theorem GlobalTheory.Ex.RecPeriods.c_psi [IsAlgClosed C] (hn : Odd n) (hN : ∀ b : N.A, ∃ γ : N.Gt, γ.b = b) {g' : ℕ} (ht : N'.Tors n g')
    {e : N.X ≃+ N'.X} (hB : μ.B e) (hT : μ.Term e) {I : NumB.Iso N.toNumB N'.toNumB} (hI : μ.OnB I)
    (p₁ : N.QT (n ^ 1)) : N'.c (e p₁.1.1.toAdd) = I.φ (N.c p₁.1.1.toAdd) ∧
      (I.lam * (N'.ψ (e p₁.1.1.toAdd) * I.h (N.c p₁.1.1.toAdd)) : Cˣ) = μ.c₀ * N.ψ p₁.1.1.toAdd := by sorry
